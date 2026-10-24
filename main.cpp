#include <Arduino.h>
#include <WiFi.h>
#include <esp32-hal-psram.h>
#include <esp_heap_caps.h>
#include <esp_wifi.h>
#include <esp_task_wdt.h>
#include <nvs_flash.h>
#include <nvs.h>
#include <mdns.h>
#include <lwip/sockets.h>
#include <lwip/dns.h>
#include <errno.h>
#include <stdarg.h>
#include "sdkconfig.h"

#if __has_include("secrets.h")
  #include "secrets.h"
#endif

#ifndef SECRET_WIFI_SSID
  #define SECRET_WIFI_SSID     "Your_WiFi_SSID"
  #define SECRET_WIFI_PASSWORD "Your_WiFi_Password"
#endif

#ifndef CONFIG_LWIP_MAX_SOCKETS
  #define CONFIG_LWIP_MAX_SOCKETS -1
#endif
#ifndef CONFIG_LWIP_MAX_ACTIVE_TCP
  #define CONFIG_LWIP_MAX_ACTIVE_TCP -1
#endif
#ifndef CONFIG_LWIP_MAX_LISTENING_TCP
  #define CONFIG_LWIP_MAX_LISTENING_TCP -1
#endif
#ifndef CONFIG_LWIP_TCP_MSL
  #define CONFIG_LWIP_TCP_MSL -1
#endif
#ifndef CONFIG_LWIP_TCP_WND_DEFAULT
  #define CONFIG_LWIP_TCP_WND_DEFAULT -1
#endif
#ifndef CONFIG_LWIP_TCP_SND_BUF_DEFAULT
  #define CONFIG_LWIP_TCP_SND_BUF_DEFAULT -1
#endif

// --- НАСТРОЙКИ СЕТИ ---
const char* WIFI_SSID     = SECRET_WIFI_SSID;
const char* WIFI_PASSWORD = SECRET_WIFI_PASSWORD;

const IPAddress STATIC_IP(192, 168, 31, 150);
const IPAddress GATEWAY_IP(192, 168, 31, 1);
const IPAddress SUBNET_MASK(255, 255, 255, 0);
const IPAddress DNS_SERVER_1(1, 1, 1, 1);
const IPAddress DNS_SERVER_2(8, 8, 8, 8);

const uint16_t PROXY_PORT = 8080;
WiFiServer proxyServer(PROXY_PORT, 16);

// --- ПУЛ СЛОТОВ И БУФЕРОВ В PSRAM ---
const int MAX_CLIENTS = 8;
const size_t STREAM_BUF_SIZE = 16384;
const size_t HELLO_BUF_SIZE  = 2048;

SemaphoreHandle_t clientSlots;
SemaphoreHandle_t slotMaskMutex;
SemaphoreHandle_t logMutex;
SemaphoreHandle_t cacheMutex;
SemaphoreHandle_t dnsMutex;

bool slotInUse[MAX_CLIENTS];
uint8_t* streamPool[MAX_CLIENTS];
uint8_t* helloPool[MAX_CLIENTS];

volatile uint32_t minStackFreeBytes = 10240;
uint32_t csrfToken = 0;

volatile int forcedStrategy = -1;
volatile uint32_t emaTtfbMs = 75;

const int NUM_STRATEGIES = 5;
const char* STRAT_NAMES[NUM_STRATEGIES] = {
    "S0:Direct",
    "S1:TLSRECx3(sub+mid)",
    "S2:Split(1+sub+mid)",
    "S3:TLSRECx3+Split",
    "S4:Disorder(TTL1)"
};

uint8_t autoOrder[4] = { 3, 1, 2, 4 };
int32_t stratScore[NUM_STRATEGIES] = { 0, 10, 10, 25, 10 };

struct HostCacheEntry {
    char key[40];
    uint8_t strat;
    uint8_t consecFails;
    uint16_t okCount;
    uint16_t failCount;
    bool useAltGfeIp;
    uint32_t lastUsedMs;
};

const int CACHE_SIZE = 64;
HostCacheEntry hostCache[CACHE_SIZE];

const uint32_t NVS_BLOB_MAGIC = 0xAD530009;
struct NvsSnapshot {
    uint32_t magic;
    int32_t forcedStrat;
    uint32_t gfeIp;
    int32_t scores[NUM_STRATEGIES];
    HostCacheEntry entries[CACHE_SIZE];
};

volatile bool nvsDirty = false;
volatile bool nvsForceSave = false;
bool initialNvsSaved = false;
unsigned long lastNvsSaveMs = 0;
const unsigned long NVS_SAVE_INTERVAL_MS = 20UL * 60UL * 1000UL;

IPAddress lastWorkingGfeIp(142, 251, 154, 4);

struct DnsEntry {
    char host[48];
    uint32_t ip;
    uint32_t exp;
};
static DnsEntry dnsCache[32];
static int dnsNext = 0;
volatile uint32_t dnsCacheHits = 0;

const int LOG_LINES = 24;
const int LOG_LINE_LEN = 112;
char logs[LOG_LINES][LOG_LINE_LEN];
int logIndex = 0;

void logPrintf(const char* fmt, ...) {
    char msg[96];
    va_list args;
    va_start(args, fmt);
    vsnprintf(msg, sizeof(msg), fmt, args);
    va_end(args);

    for (size_t i = 0; msg[i] != '\0'; i++) {
        if ((uint8_t)msg[i] < 0x20 || msg[i] == 0x7F) msg[i] = ' ';
    }

    char fullLine[LOG_LINE_LEN];
    snprintf(fullLine, sizeof(fullLine), "%lus | %s", millis() / 1000UL, msg);

    #if ARDUINO_USB_CDC_ON_BOOT
      Serial0.println(fullLine);
      Serial.println(fullLine);
    #else
      Serial.println(fullLine);
    #endif

    if (xSemaphoreTake(logMutex, 30 / portTICK_PERIOD_MS) == pdTRUE) {
        strncpy(logs[logIndex], fullLine, LOG_LINE_LEN - 1);
        logs[logIndex][LOG_LINE_LEN - 1] = '\0';
        logIndex = (logIndex + 1) % LOG_LINES;
        xSemaphoreGive(logMutex);
    }
}

int acquireSlotIndex() {
    int idx = -1;
    if (xSemaphoreTake(slotMaskMutex, 50 / portTICK_PERIOD_MS) == pdTRUE) {
        for (int i = 0; i < MAX_CLIENTS; i++) {
            if (!slotInUse[i]) {
                slotInUse[i] = true;
                idx = i;
                break;
            }
        }
        xSemaphoreGive(slotMaskMutex);
    }
    return idx;
}

void releaseSlotIndex(int idx) {
    if (idx < 0 || idx >= MAX_CLIENTS) return;
    if (xSemaphoreTake(slotMaskMutex, 50 / portTICK_PERIOD_MS) == pdTRUE) {
        slotInUse[idx] = false;
        xSemaphoreGive(slotMaskMutex);
    }
}

void applyCleanDns() {
    ip_addr_t d1, d2;
    IP_ADDR4(&d1, 1, 1, 1, 1);
    IP_ADDR4(&d2, 8, 8, 8, 8);
    dns_setserver(0, &d1);
    dns_setserver(1, &d2);
}

void configureSocketTimeoutsAndKeepalive(int fd) {
    if (fd < 0) return;
    int flag = 1, idle = 30, intvl = 10, cnt = 3;
    setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &flag, sizeof(flag));
    setsockopt(fd, SOL_SOCKET, SO_KEEPALIVE, &flag, sizeof(flag));
    setsockopt(fd, IPPROTO_TCP, TCP_KEEPIDLE, &idle, sizeof(idle));
    setsockopt(fd, IPPROTO_TCP, TCP_KEEPINTVL, &intvl, sizeof(intvl));
    setsockopt(fd, IPPROTO_TCP, TCP_KEEPCNT, &cnt, sizeof(cnt));

    struct timeval sndTv = { 10, 0 };
    setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &sndTv, sizeof(sndTv));
}

void closeSocketAbort(WiFiClient& c) {
    int fd = c.fd();
    if (fd >= 0) {
        struct linger sl = { 1, 0 };
        setsockopt(fd, SOL_SOCKET, SO_LINGER, &sl, sizeof(sl));
    }
    c.stop();
}

void closeSocketGraceful(WiFiClient& c) {
    int fd = c.fd();
    if (fd >= 0) {
        shutdown(fd, SHUT_WR);
        uint8_t drain[64];
        unsigned long start = millis();
        while (millis() - start < 150) {
            int r = recv(fd, drain, sizeof(drain), MSG_DONTWAIT);
            if (r == 0) break;
            if (r < 0 && errno != EAGAIN && errno != EWOULDBLOCK) break;
            vTaskDelay(5 / portTICK_PERIOD_MS);
        }
    }
    c.stop();
}

bool isPrivateOrReservedIp(const IPAddress& ip) {
    uint8_t a = ip[0], b = ip[1];
    if (a == 0 || a == 10 || a == 127) return true;
    if (a == 192 && b == 168) return true;
    if (a == 172 && b >= 16 && b <= 31) return true;
    if (a == 169 && b == 254) return true;
    if (a == 100 && b >= 64 && b <= 127) return true;
    if (a >= 224) return true;
    return false;
}

bool isValidHostname(const char* h) {
    if (!h || h[0] == '\0' || h[0] == '.' || h[0] == '-') return false;
    size_t len = strlen(h);
    if (len > 253) return false;
    for (size_t i = 0; i < len; i++) {
        char c = h[i];
        bool ok = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
                  (c >= '0' && c <= '9') || (c == '.') || (c == '-');
        if (!ok) return false;
    }
    return (h[len - 1] != '-');
}

bool resolveHostSafe(const char* host, IPAddress& outIp) {
    if (outIp.fromString(host)) return true;
    if (xSemaphoreTake(dnsMutex, 4000 / portTICK_PERIOD_MS) != pdTRUE) return false;

    uint32_t now = millis();
    for (auto& e : dnsCache) {
        if (e.ip && (int32_t)(e.exp - now) > 0 && strncmp(e.host, host, 47) == 0) {
            outIp = IPAddress(e.ip);
            dnsCacheHits++;
            xSemaphoreGive(dnsMutex);
            return true;
        }
    }

    bool ok = (WiFi.hostByName(host, outIp) == 1);
    if (ok) {
        DnsEntry& e = dnsCache[dnsNext++ % 32];
        strncpy(e.host, host, 47);
        e.host[47] = '\0';
        e.ip = (uint32_t)outIp;
        e.exp = now + 120000UL;
    }
    xSemaphoreGive(dnsMutex);
    return ok;
}

const char* BASE_PAC_DOMAINS[] = {
    "youtube.com", "googlevideo.com", "ytimg.com", "ggpht.com", "gvt1.com",
    "youtu.be", "youtubei.googleapis.com", "youtube.googleapis.com",
    "jnn-pa.googleapis.com", "googleusercontent.com", "youtube-nocookie.com", "widevine.com",
    "discord.com", "discordapp.com", "discordapp.net", "discord.gg", "discord.media", "discordapp.io",
    "instagram.com", "cdninstagram.com", "fbcdn.net", "facebook.com"
};
const size_t BASE_PAC_COUNT = sizeof(BASE_PAC_DOMAINS) / sizeof(BASE_PAC_DOMAINS[0]);

const char* EXCLUDE_DOMAINS[] = {
    "ru", "su", "by", "kz", "yandex.net", "vk.com", "gosuslugi.ru", "sberbank.ru"
};
const size_t EXCLUDE_COUNT = sizeof(EXCLUDE_DOMAINS) / sizeof(EXCLUDE_DOMAINS[0]);

bool hasDomainSuffix(const String& h, const char* domain) {
    size_t hLen = h.length();
    size_t dLen = strlen(domain);
    if (hLen == dLen) return h.equalsIgnoreCase(domain);
    if (hLen > dLen + 1 && h.endsWith(domain) && h[hLen - dLen - 1] == '.') return true;
    return false;
}

bool isExcludedHost(const String& host) {
    String h = host;
    h.toLowerCase();
    for (size_t i = 0; i < EXCLUDE_COUNT; i++) {
        if (hasDomainSuffix(h, EXCLUDE_DOMAINS[i])) return true;
    }
    return false;
}

bool isGoogleFrontEndHost(const String& host) {
    return (hasDomainSuffix(host, "youtube.com") ||
            hasDomainSuffix(host, "googleapis.com") ||
            hasDomainSuffix(host, "ytimg.com") ||
            hasDomainSuffix(host, "ggpht.com") ||
            hasDomainSuffix(host, "youtu.be") ||
            host.equalsIgnoreCase("redirector.googlevideo.com"));
}

String normalizeHostKey(const String& host) {
    String h = host;
    h.toLowerCase();
    if (h.endsWith(".googlevideo.com") && h != "redirector.googlevideo.com") {
        int snIdx = h.indexOf("sn-");
        if (snIdx >= 0) {
            String cluster = h.substring(snIdx, min((int)h.length(), snIdx + 8));
            int dotPos = cluster.indexOf('.');
            if (dotPos > 0) cluster = cluster.substring(0, dotPos);
            return cluster + ".googlevideo.com";
        }
        return "googlevideo.com";
    }
    int lastDot = h.lastIndexOf('.');
    if (lastDot > 0) {
        int prevDot = h.lastIndexOf('.', lastDot - 1);
        if (prevDot > 0) {
            String sld = h.substring(prevDot + 1);
            if (sld == "googleapis.com" || sld == "co.uk" || sld == "com.tr") {
                int thirdDot = h.lastIndexOf('.', prevDot - 1);
                if (thirdDot >= 0) return h.substring(thirdDot + 1);
                return h;
            }
            return sld;
        }
    }
    return h;
}

void rebuildAutoOrder() {
    uint8_t candidates[4] = { 3, 1, 2, 4 };
    for (int i = 0; i < 3; i++) {
        for (int j = i + 1; j < 4; j++) {
            if (stratScore[candidates[j]] > stratScore[candidates[i]]) {
                uint8_t tmp = candidates[i];
                candidates[i] = candidates[j];
                candidates[j] = tmp;
            }
        }
    }
    for (int i = 0; i < 4; i++) autoOrder[i] = candidates[i];
}

void saveCacheToNvs() {
    NvsSnapshot* snap = (NvsSnapshot*)(psramFound() ? ps_malloc(sizeof(NvsSnapshot)) : malloc(sizeof(NvsSnapshot)));
    if (!snap) return;

    if (xSemaphoreTake(cacheMutex, 100 / portTICK_PERIOD_MS) != pdTRUE) {
        free(snap);
        return;
    }
    snap->magic = NVS_BLOB_MAGIC;
    snap->forcedStrat = forcedStrategy;
    snap->gfeIp = (uint32_t)lastWorkingGfeIp;
    memcpy(snap->scores, stratScore, sizeof(stratScore));
    memcpy(snap->entries, hostCache, sizeof(hostCache));
    nvsDirty = false;
    nvsForceSave = false;
    initialNvsSaved = true;
    lastNvsSaveMs = millis();
    xSemaphoreGive(cacheMutex);

    nvs_handle_t h;
    if (nvs_open("antidpi", NVS_READWRITE, &h) == ESP_OK) {
        nvs_set_blob(h, "snap_yt_v1", snap, sizeof(NvsSnapshot));
        nvs_commit(h);
        nvs_close(h);
    }
    free(snap);
}

void loadCacheFromNvs() {
    NvsSnapshot* snap = (NvsSnapshot*)(psramFound() ? ps_malloc(sizeof(NvsSnapshot)) : malloc(sizeof(NvsSnapshot)));
    if (!snap) return;

    nvs_handle_t h;
    if (nvs_open("antidpi", NVS_READONLY, &h) == ESP_OK) {
        size_t sz = sizeof(NvsSnapshot);
        if (nvs_get_blob(h, "snap_yt_v1", snap, &sz) == ESP_OK && snap->magic == NVS_BLOB_MAGIC) {
            if (snap->forcedStrat >= -1 && snap->forcedStrat < NUM_STRATEGIES) forcedStrategy = snap->forcedStrat;
            if (snap->gfeIp != 0 && !isPrivateOrReservedIp(IPAddress(snap->gfeIp))) lastWorkingGfeIp = IPAddress(snap->gfeIp);
            memcpy(stratScore, snap->scores, sizeof(stratScore));
            memcpy(hostCache, snap->entries, sizeof(hostCache));
            uint32_t now = millis();
            for (int i = 0; i < CACHE_SIZE; i++) {
                hostCache[i].lastUsedMs = now;
                hostCache[i].consecFails = 0;
            }
            rebuildAutoOrder();
            initialNvsSaved = true;
            logPrintf("NVS loaded! Leader: %s", STRAT_NAMES[autoOrder[0]]);
        }
        nvs_close(h);
    }
    free(snap);
}

uint8_t getHostStrategy(const String& host, bool& useAltIp) {
    useAltIp = false;
    if (isExcludedHost(host)) return 0;
    if (forcedStrategy >= 0 && forcedStrategy < NUM_STRATEGIES) return (uint8_t)forcedStrategy;

    String key = normalizeHostKey(host);
    uint8_t res = autoOrder[0];

    if (xSemaphoreTake(cacheMutex, 50 / portTICK_PERIOD_MS) == pdTRUE) {
        int freeIdx = -1, oldestIdx = 0;
        uint32_t oldestTime = 0xFFFFFFFF;

        for (int i = 0; i < CACHE_SIZE; i++) {
            if (hostCache[i].key[0] != '\0' && strncmp(hostCache[i].key, key.c_str(), 39) == 0) {
                hostCache[i].lastUsedMs = millis();
                res = hostCache[i].strat;
                useAltIp = hostCache[i].useAltGfeIp;
                xSemaphoreGive(cacheMutex);
                return res;
            }
            if (hostCache[i].key[0] == '\0' && freeIdx < 0) freeIdx = i;
            if (hostCache[i].lastUsedMs < oldestTime) {
                oldestTime = hostCache[i].lastUsedMs;
                oldestIdx = i;
            }
        }

        int targetIdx = (freeIdx >= 0) ? freeIdx : oldestIdx;
        strncpy(hostCache[targetIdx].key, key.c_str(), 39);
        hostCache[targetIdx].key[39] = '\0';
        hostCache[targetIdx].strat = autoOrder[0];
        hostCache[targetIdx].consecFails = 0;
        hostCache[targetIdx].okCount = 0;
        hostCache[targetIdx].failCount = 0;
        hostCache[targetIdx].useAltGfeIp = false;
        hostCache[targetIdx].lastUsedMs = millis();
        res = hostCache[targetIdx].strat;
        xSemaphoreGive(cacheMutex);
    }
    return res;
}

void enableGfeIpFailoverOnly(const String& host, bool& useAltIp) {
    if (!isGoogleFrontEndHost(host)) return;
    String key = normalizeHostKey(host);
    if (xSemaphoreTake(cacheMutex, 50 / portTICK_PERIOD_MS) == pdTRUE) {
        for (int i = 0; i < CACHE_SIZE; i++) {
            if (hostCache[i].key[0] != '\0' && strncmp(hostCache[i].key, key.c_str(), 39) == 0) {
                hostCache[i].useAltGfeIp = true;
                useAltIp = true;
                break;
            }
        }
        xSemaphoreGive(cacheMutex);
    }
}

uint8_t reportHostFailure(const String& host, uint8_t usedStrat, bool& useAltIp) {
    uint8_t nextStrat = usedStrat;
    if (isExcludedHost(host) || forcedStrategy >= 0) return nextStrat;

    String key = normalizeHostKey(host);
    if (xSemaphoreTake(cacheMutex, 50 / portTICK_PERIOD_MS) == pdTRUE) {
        for (int i = 0; i < CACHE_SIZE; i++) {
            if (hostCache[i].key[0] != '\0' && strncmp(hostCache[i].key, key.c_str(), 39) == 0) {
                hostCache[i].failCount++;
                hostCache[i].consecFails++;

                if (isGoogleFrontEndHost(host) && !hostCache[i].useAltGfeIp) {
                    hostCache[i].useAltGfeIp = true;
                    hostCache[i].consecFails = 0;
                    useAltIp = true;
                    hostCache[i].strat = autoOrder[0];
                    nextStrat = autoOrder[0];
                    xSemaphoreGive(cacheMutex);
                    logPrintf("[GFE-FAILOVER] %s -> %s", key.c_str(), lastWorkingGfeIp.toString().c_str());
                    return nextStrat;
                }

                if (hostCache[i].okCount > 0 && hostCache[i].consecFails < 2) {
                    nextStrat = hostCache[i].strat;
                    useAltIp = hostCache[i].useAltGfeIp;
                    xSemaphoreGive(cacheMutex);
                    return nextStrat;
                }

                hostCache[i].consecFails = 0;
                if (usedStrat < NUM_STRATEGIES && stratScore[usedStrat] > -50) {
                    stratScore[usedStrat] -= 1;
                    rebuildAutoOrder();
                }

                int nextPos = 0;
                for (int k = 0; k < 4; k++) {
                    if (autoOrder[k] == usedStrat) {
                        nextPos = (k + 1) % 4;
                        break;
                    }
                }
                nextStrat = autoOrder[nextPos];
                hostCache[i].strat = nextStrat;
                useAltIp = hostCache[i].useAltGfeIp;
                xSemaphoreGive(cacheMutex);
                logPrintf("[ROTATE] %s: %s -> %s", key.c_str(), STRAT_NAMES[usedStrat], STRAT_NAMES[nextStrat]);
                return nextStrat;
            }
        }
        xSemaphoreGive(cacheMutex);
    }
    return nextStrat;
}

void reportHostSuccess(const String& host, uint8_t usedStrat, const IPAddress& connectedIp, unsigned long ttfbMs) {
    if (isExcludedHost(host)) return;
    if (usedStrat != 4 && ttfbMs > 5 && ttfbMs < 1000) {
        emaTtfbMs = (emaTtfbMs * 3 + (uint32_t)ttfbMs) / 4;
    }

    String key = normalizeHostKey(host);
    if (xSemaphoreTake(cacheMutex, 50 / portTICK_PERIOD_MS) == pdTRUE) {
        if (usedStrat < NUM_STRATEGIES && stratScore[usedStrat] < 500) {
            stratScore[usedStrat] += 1;
            rebuildAutoOrder();
        }
        if (isGoogleFrontEndHost(host) && !host.equalsIgnoreCase("redirector.googlevideo.com")) {
            lastWorkingGfeIp = connectedIp;
        }
        for (int i = 0; i < CACHE_SIZE; i++) {
            if (hostCache[i].key[0] != '\0' && strncmp(hostCache[i].key, key.c_str(), 39) == 0) {
                if (hostCache[i].okCount == 0 || hostCache[i].consecFails > 0) nvsDirty = true;
                hostCache[i].consecFails = 0;
                hostCache[i].okCount++;
                break;
            }
        }
        xSemaphoreGive(cacheMutex);
    }
}

bool sendAll(int sockFd, const uint8_t* data, size_t len, int flags = 0) {
    size_t totalSent = 0;
    unsigned long lastProgressMs = millis();
    while (totalSent < len) {
        int n = send(sockFd, data + totalSent, len - totalSent, flags);
        if (n > 0) {
            totalSent += (size_t)n;
            lastProgressMs = millis();
            continue;
        }
        if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK || errno == EINTR)) {
            if (millis() - lastProgressMs > 25000UL) return false;
            vTaskDelay(2 / portTICK_PERIOD_MS);
            continue;
        }
        return false;
    }
    return true;
}

bool recvExactFd(int fd, uint8_t* buf, size_t count, uint32_t timeoutMs = 3000) {
    size_t got = 0;
    unsigned long start = millis();
    while (got < count && (millis() - start < timeoutMs)) {
        fd_set rfd;
        FD_ZERO(&rfd);
        FD_SET(fd, &rfd);
        struct timeval tv = { 0, 50000 };
        int s = select(fd + 1, &rfd, NULL, NULL, &tv);
        if (s > 0) {
            int r = recv(fd, buf + got, count - got, 0);
            if (r <= 0) return false;
            got += (size_t)r;
        } else if (s < 0) {
            return false;
        }
    }
    return (got == count);
}

bool findSni(const uint8_t* data, size_t len, int& sniOffset, int& sniLen) {
    sniOffset = -1;
    sniLen = 0;
    if (len < 64 || data[0] != 0x16 || data[1] != 0x03 || data[5] != 0x01) return false;
    size_t pos = 43;
    if (pos >= len) return false;

    pos += 1 + data[pos];
    if (pos + 2 > len) return false;

    pos += 2 + ((data[pos] << 8) | data[pos + 1]);
    if (pos + 1 > len) return false;

    pos += 1 + data[pos];
    if (pos + 2 > len) return false;

    size_t ext_end = pos + 2 + ((data[pos] << 8) | data[pos + 1]);
    pos += 2;
    if (ext_end > len) ext_end = len;

    while (pos + 4 <= ext_end) {
        uint16_t ext_type = (data[pos] << 8) | data[pos + 1];
        uint16_t ext_len  = (data[pos + 2] << 8) | data[pos + 3];
        pos += 4;

        if (ext_type == 0x0000) {
            if (pos + 5 <= ext_end) {
                uint16_t nameLen = (data[pos + 3] << 8) | data[pos + 4];
                size_t offset = pos + 5;
                if (nameLen >= 3 && offset + nameLen <= len) {
                    sniOffset = (int)offset;
                    sniLen = (int)nameLen;
                    return true;
                }
            }
            return false;
        }
        if (pos + ext_len > ext_end) return false;
        pos += ext_len;
    }
    return false;
}

void calcSniCuts(const uint8_t* host, size_t len, int& cutSub, int& cutMid) {
    int firstDot = -1, lastDot = -1, prevDot = -1;
    for (size_t i = 0; i < len; i++) {
        if (host[i] == '.') {
            if (firstDot < 0) firstDot = (int)i;
            prevDot = lastDot;
            lastDot = (int)i;
        }
    }
    int startSld = prevDot + 1;
    int endSld = (lastDot < 0) ? (int)len : lastDot;
    cutMid = startSld + (endSld - startSld) / 2;

    if (firstDot >= 2 && firstDot < startSld) {
        cutSub = firstDot / 2;
    } else {
        cutSub = 2;
    }
    if (cutSub >= cutMid) {
        cutSub = (cutMid > 2) ? (cutMid / 2) : 1;
    }
}

bool executeClientHelloBypass(int sockFd, const uint8_t* buffer, size_t len, uint8_t strat, const char* hostStr, const IPAddress& ip) {
    if (strat == 0 || len < 64) return sendAll(sockFd, buffer, len, 0);

    int sniOff = -1, sniLen = 0;
    bool hasSni = findSni(buffer, len, sniOff, sniLen);
    if (!hasSni || sniOff < 43 || sniLen < 3) return sendAll(sockFd, buffer, len, 0);

    int relSub = 1, relMid = 2;
    calcSniCuts(buffer + sniOff, (size_t)sniLen, relSub, relMid);

    size_t cut1 = (size_t)(sniOff + relSub);
    size_t cut2 = (size_t)(sniOff + relMid);
    size_t pos1 = 6;

    if (cut1 <= pos1 || cut2 <= cut1 || cut2 + 1 >= len || len > STREAM_BUF_SIZE - 16) {
        return sendAll(sockFd, buffer, len, 0);
    }

    bool ok = false;
    if (strat == 1 || strat == 3) {
        size_t p1Len = cut1 - 5;
        size_t p2Len = cut2 - cut1;
        size_t p3Len = len - cut2;

        uint8_t* outBuf = (uint8_t*)(psramFound() ? ps_malloc(len + 10) : malloc(len + 10));
        if (!outBuf) return false;

        outBuf[0] = 0x16; outBuf[1] = buffer[1]; outBuf[2] = buffer[2];
        outBuf[3] = (p1Len >> 8) & 0xFF; outBuf[4] = p1Len & 0xFF;
        memcpy(outBuf + 5, buffer + 5, p1Len);

        size_t r2 = 5 + p1Len;
        outBuf[r2 + 0] = 0x16; outBuf[r2 + 1] = buffer[1]; outBuf[r2 + 2] = buffer[2];
        outBuf[r2 + 3] = (p2Len >> 8) & 0xFF; outBuf[r2 + 4] = p2Len & 0xFF;
        memcpy(outBuf + r2 + 5, buffer + cut1, p2Len);

        size_t r3 = r2 + 5 + p2Len;
        outBuf[r3 + 0] = 0x16; outBuf[r3 + 1] = buffer[1]; outBuf[r3 + 2] = buffer[2];
        outBuf[r3 + 3] = (p3Len >> 8) & 0xFF; outBuf[r3 + 4] = p3Len & 0xFF;
        memcpy(outBuf + r3 + 5, buffer + cut2, p3Len);

        if (strat == 1) {
            ok = sendAll(sockFd, outBuf, r2, 0);
            vTaskDelay(3 / portTICK_PERIOD_MS);
            ok = ok && sendAll(sockFd, outBuf + r2, r3 - r2, 0);
            vTaskDelay(3 / portTICK_PERIOD_MS);
            ok = ok && sendAll(sockFd, outBuf + r3, 5 + p3Len, 0);
        } else {
            ok = sendAll(sockFd, outBuf, pos1, 0);
            vTaskDelay(3 / portTICK_PERIOD_MS);
            ok = ok && sendAll(sockFd, outBuf + pos1, r2 - pos1, 0);
            vTaskDelay(3 / portTICK_PERIOD_MS);
            ok = ok && sendAll(sockFd, outBuf + r2, r3 - r2, 0);
            vTaskDelay(3 / portTICK_PERIOD_MS);
            ok = ok && sendAll(sockFd, outBuf + r3, 5 + p3Len, 0);
        }
        free(outBuf);
    } else if (strat == 2) {
        ok = sendAll(sockFd, buffer, pos1, 0);
        vTaskDelay(3 / portTICK_PERIOD_MS);
        ok = ok && sendAll(sockFd, buffer + pos1, cut1 - pos1, 0);
        vTaskDelay(3 / portTICK_PERIOD_MS);
        ok = ok && sendAll(sockFd, buffer + cut1, cut2 - cut1, 0);
        vTaskDelay(3 / portTICK_PERIOD_MS);
        ok = ok && sendAll(sockFd, buffer + cut2, len - cut2, 0);
    } else if (strat == 4) {
        int ttlLow = 1, ttlNorm = 64;
        setsockopt(sockFd, IPPROTO_IP, IP_TTL, &ttlLow, sizeof(ttlLow));
        ok = sendAll(sockFd, buffer, cut1, 0);
        setsockopt(sockFd, IPPROTO_IP, IP_TTL, &ttlNorm, sizeof(ttlNorm));
        vTaskDelay(2 / portTICK_PERIOD_MS);
        ok = ok && sendAll(sockFd, buffer + cut1, cut2 - cut1, 0);
        vTaskDelay(2 / portTICK_PERIOD_MS);
        ok = ok && sendAll(sockFd, buffer + cut2, len - cut2, 0);
    } else {
        ok = sendAll(sockFd, buffer, len, 0);
    }

    logPrintf("[%s] %s [%s] len=%u sni=%d cuts=%u,%u",
              STRAT_NAMES[strat], hostStr, ip.toString().c_str(), (unsigned)len, sniOff, (unsigned)cut1, (unsigned)cut2);
    return ok;
}

// --- ВЕБ-ПАНЕЛЬ И PAC ---

String generatePacScript() {
    String myIp = WiFi.localIP().toString();
    String pac;
    pac.reserve(1024);
    pac += "var DOMS=[\n";
    for (size_t i = 0; i < BASE_PAC_COUNT; i++) {
        pac += "\"";
        pac += BASE_PAC_DOMAINS[i];
        pac += "\"";
        if (i + 1 < BASE_PAC_COUNT) pac += ",";
    }
    pac += "];\n";
    pac += "function FindProxyForURL(url, host) {\n";
    pac += "  var h = host.toLowerCase();\n";
    pac += "  if (isPlainHostName(h) || shExpMatch(h, '192.168.*') || shExpMatch(h, '127.*') || shExpMatch(h, '*.ru') || shExpMatch(h, '*.local')) return 'DIRECT';\n";
    pac += "  for (var i = 0; i < DOMS.length; i++) {\n";
    pac += "    var d = DOMS[i];\n";
    pac += "    if (h === d || dnsDomainIs(h, '.' + d)) return 'PROXY " + myIp + ":" + String(PROXY_PORT) + "; DIRECT';\n";
    pac += "  }\n";
    pac += "  return 'DIRECT';\n";
    pac += "}\n";
    return pac;
}

String generateDashboardHtml() {
    String myIp = WiFi.localIP().toString();
    String pacUrl = "http://" + myIp + ":" + String(PROXY_PORT) + "/proxy.pac";
    uint32_t curFastTimeout = constrain(emaTtfbMs * 10, 800UL, 1400UL);
    String tokStr = String(csrfToken, HEX);

    int slotsBusy = MAX_CLIENTS - (int)uxSemaphoreGetCount(clientSlots);

    String html;
    html.reserve(5500);
    html += "<!DOCTYPE html><html><head><meta charset='utf-8'><title>ESP32-S3 YouTube AntiDPI</title>";
    html += "<style>body{font-family:sans-serif;background:#121212;color:#eee;padding:15px;max-width:840px;margin:auto;}";
    html += ".card{background:#1e1e1e;padding:15px;border-radius:10px;margin-bottom:15px;}";
    html += ".btn{display:inline-block;padding:7px 12px;margin:3px;background:#2c2c2c;color:#fff;text-decoration:none;border-radius:6px;font-size:13px;}";
    html += ".btn.active{background:#00bcd4;font-weight:bold;}";
    html += "input{width:95%;padding:8px;background:#2a2a2a;color:#00ffcc;border:none;border-radius:6px;text-align:center;margin-top:5px;}";
    html += "pre{background:#0b0c10;color:#00ffcc;padding:10px;border-radius:6px;overflow-x:auto;font-size:12px;line-height:1.4;}</style></head><body>";

    html += "<div class='card'><h3>ESP32-S3 YouTube AntiDPI Proxy (" + myIp + ":" + String(PROXY_PORT) + ")</h3>";
    html += "<p style='font-size:12px;color:#aaa;'>"
            "<b>Slots busy: " + String(slotsBusy) + "/" + String(MAX_CLIENTS) + "</b> | "
            "DNS Cache Hits: " + String(dnsCacheHits) + "<br>"
            "SRAM: " + String(ESP.getFreeHeap() / 1024) + " KB | PSRAM: " + String(ESP.getFreePsram() / 1024) +
            " KB | MinStack: " + String(minStackFreeBytes) + " B | EMA TTFB: " + String(emaTtfbMs) + " ms (TO: " + String(curFastTimeout) + " ms)</p>";

    html += "<div><b>Bypass Strategy:</b> ";
    html += "<a class='btn " + String(forcedStrategy == -1 ? "active" : "") + "' href='/set?s=-1&t=" + tokStr + "'>AUTO (" + String(STRAT_NAMES[autoOrder[0]]) + ")</a>";
    for (int i = 0; i < NUM_STRATEGIES; i++) {
        html += "<a class='btn " + String(forcedStrategy == i ? "active" : "") + "' href='/set?s=" + String(i) + "&t=" + tokStr + "'>" + String(STRAT_NAMES[i]) + "</a>";
    }
    html += "</div><div style='margin-top:8px;'>";
    html += "<a class='btn' style='background:#2e7d32' href='/set?save=1&t=" + tokStr + "'>Save Cache to NVS</a></div>";
    html += "<p style='font-size:13px;color:#ccc;margin-bottom:0;'>PAC URL / HTTP Proxy Port 8080:<br><input type='text' value='" + pacUrl + "' readonly></p></div>";

    html += "<div class='card'><b>Live Log (<a href='/' style='color:#00bcd4'>Refresh</a>):</b><pre>";
    if (xSemaphoreTake(logMutex, 100 / portTICK_PERIOD_MS) == pdTRUE) {
        for (int i = 0; i < LOG_LINES; i++) {
            int idx = (logIndex + i) % LOG_LINES;
            if (logs[idx][0] != '\0') {
                for (size_t cIdx = 0; logs[idx][cIdx] != '\0'; cIdx++) {
                    char ch = logs[idx][cIdx];
                    if (ch == '<') html += "&lt;";
                    else if (ch == '>') html += "&gt;";
                    else if (ch == '&') html += "&amp;";
                    else html += ch;
                }
                html += "\n";
            }
        }
        xSemaphoreGive(logMutex);
    }
    html += "</pre></div></body></html>";
    return html;
}

void handleDirectHttpOnProxyPort(WiFiClient& client, const char* firstLine) {
    const char* sp1 = strchr(firstLine, ' ');
    if (!sp1) { closeSocketAbort(client); return; }
    const char* uriStart = sp1 + 1;
    const char* sp2 = strchr(uriStart, ' ');
    String uri = sp2 ? String(uriStart).substring(0, sp2 - uriStart) : String(uriStart);

    if (uri.startsWith("http://")) {
        String httpsUrl = "https://" + uri.substring(7);
        String redir = "HTTP/1.1 308 Permanent Redirect\r\nLocation: " + httpsUrl + "\r\nConnection: close\r\n\r\n";
        sendAll(client.fd(), (const uint8_t*)redir.c_str(), redir.length(), 0);
        closeSocketGraceful(client);
        return;
    }

    if (uri.startsWith("/proxy.pac")) {
        String pac = generatePacScript();
        String hdr = "HTTP/1.1 200 OK\r\nContent-Type: application/x-ns-proxy-autoconfig\r\nContent-Length: " +
                     String(pac.length()) + "\r\nConnection: close\r\n\r\n";
        sendAll(client.fd(), (const uint8_t*)hdr.c_str(), hdr.length(), 0);
        sendAll(client.fd(), (const uint8_t*)pac.c_str(), pac.length(), 0);
        closeSocketGraceful(client);
        return;
    }

    if (uri.startsWith("/set?")) {
        String expectedTok = "t=" + String(csrfToken, HEX);
        if (uri.indexOf(expectedTok) < 0) {
            const char* forb = "HTTP/1.1 403 Forbidden\r\nConnection: close\r\n\r\nInvalid CSRF token";
            sendAll(client.fd(), (const uint8_t*)forb, strlen(forb), 0);
            closeSocketGraceful(client);
            return;
        }
        int sIdx = uri.indexOf("s=");
        if (sIdx >= 0) {
            int endIdx = uri.indexOf('&', sIdx);
            String val = (endIdx > 0) ? uri.substring(sIdx + 2, endIdx) : uri.substring(sIdx + 2);
            int s = val.toInt();
            if (s >= -1 && s < NUM_STRATEGIES) {
                forcedStrategy = s;
                nvsDirty = true;
                logPrintf(s == -1 ? "=== Mode: AUTO-DPI ===" : "=== Forced: %s ===", (s == -1 ? "" : STRAT_NAMES[s]));
            }
        }
        if (uri.indexOf("save=1") >= 0) {
            nvsForceSave = true;
            logPrintf("=== NVS save scheduled ===");
        }
        const char* redir = "HTTP/1.1 302 Found\r\nLocation: /\r\nConnection: close\r\n\r\n";
        sendAll(client.fd(), (const uint8_t*)redir, strlen(redir), 0);
        closeSocketGraceful(client);
        return;
    }

    String html = generateDashboardHtml();
    String hdr = "HTTP/1.1 200 OK\r\nContent-Type: text/html; charset=utf-8\r\nContent-Length: " +
                 String(html.length()) + "\r\nConnection: close\r\n\r\n";
    sendAll(client.fd(), (const uint8_t*)hdr.c_str(), hdr.length(), 0);
    sendAll(client.fd(), (const uint8_t*)html.c_str(), html.length(), 0);
    closeSocketGraceful(client);
}

// --- ОСНОВНАЯ ФУНКЦИЯ СЕССИИ ПРОКСИ ---
void runProxySession(WiFiClient& client, int slotIdx) {
    int clientFd = client.fd();
    configureSocketTimeoutsAndKeepalive(clientFd);

    fd_set initFds;
    FD_ZERO(&initFds);
    FD_SET(clientFd, &initFds);
    struct timeval initTv = { 3, 0 };
    if (select(clientFd + 1, &initFds, NULL, NULL, &initTv) <= 0) {
        closeSocketAbort(client);
        return;
    }

    char* reqBuf = (char*)streamPool[slotIdx];
    size_t reqLen = 0;
    unsigned long startMs = millis();
    bool headerComplete = false;

    while (client.connected() && millis() - startMs < 3000 && reqLen < 1023) {
        int avail = client.available();
        if (avail > 0) {
            int c = client.read();
            if (c < 0) break;
            reqBuf[reqLen++] = (char)c;
            reqBuf[reqLen] = '\0';
            if (reqLen >= 4 && memcmp(reqBuf + reqLen - 4, "\r\n\r\n", 4) == 0) {
                headerComplete = true;
                break;
            }
        } else {
            vTaskDelay(1 / portTICK_PERIOD_MS);
        }
    }

    if (!headerComplete) {
        closeSocketAbort(client);
        return;
    }

    char* eol = strstr(reqBuf, "\r\n");
    if (eol) *eol = '\0';

    if (strncmp(reqBuf, "GET ", 4) == 0) {
        handleDirectHttpOnProxyPort(client, reqBuf);
        return;
    }

    if (strncmp(reqBuf, "CONNECT ", 8) != 0) {
        const char* badReq = "HTTP/1.1 400 Bad Request\r\nConnection: close\r\n\r\n";
        sendAll(clientFd, (const uint8_t*)badReq, strlen(badReq), 0);
        closeSocketGraceful(client);
        return;
    }

    char* targetStart = reqBuf + 8;
    char* spaceAfterTarget = strchr(targetStart, ' ');
    if (!spaceAfterTarget) { closeSocketAbort(client); return; }
    *spaceAfterTarget = '\0';

    char* colon = strchr(targetStart, ':');
    uint16_t port = 443;
    if (colon) {
        *colon = '\0';
        port = (uint16_t)atoi(colon + 1);
    }

    if (port != 443 || !isValidHostname(targetStart)) {
        const char* forb = "HTTP/1.1 403 Forbidden\r\nConnection: close\r\n\r\n";
        sendAll(clientFd, (const uint8_t*)forb, strlen(forb), 0);
        closeSocketGraceful(client);
        return;
    }

    String host = String(targetStart);
    bool useAltGfeIp = false;
    uint8_t activeStrat = getHostStrategy(host, useAltGfeIp);

    unsigned long dnsStart = millis();
    IPAddress targetIp;
    if (useAltGfeIp && isGoogleFrontEndHost(host)) {
        targetIp = lastWorkingGfeIp;
    } else if (!resolveHostSafe(host.c_str(), targetIp)) {
        logPrintf("[DNS FAIL] %s", host.c_str());
        const char* badGw = "HTTP/1.1 502 Bad Gateway\r\nConnection: close\r\n\r\n";
        sendAll(clientFd, (const uint8_t*)badGw, strlen(badGw), 0);
        closeSocketGraceful(client);
        return;
    }
    unsigned long dnsMs = millis() - dnsStart;

    if (isPrivateOrReservedIp(targetIp)) {
        logPrintf("[BLOCKED LAN IP] %s -> %s", host.c_str(), targetIp.toString().c_str());
        const char* forb = "HTTP/1.1 403 Forbidden\r\nConnection: close\r\n\r\n";
        sendAll(clientFd, (const uint8_t*)forb, strlen(forb), 0);
        closeSocketGraceful(client);
        return;
    }

    WiFiClient upstream;
    if (!upstream.connect(targetIp, port, 3000)) {
        logPrintf("[TCP FAIL] %s -> %s", host.c_str(), targetIp.toString().c_str());
        enableGfeIpFailoverOnly(host, useAltGfeIp);
        if (isGoogleFrontEndHost(host) && targetIp != lastWorkingGfeIp) {
            targetIp = lastWorkingGfeIp;
            if (!upstream.connect(targetIp, port, 2500)) {
                const char* badGw = "HTTP/1.1 502 Bad Gateway\r\nConnection: close\r\n\r\n";
                sendAll(clientFd, (const uint8_t*)badGw, strlen(badGw), 0);
                closeSocketGraceful(client);
                return;
            }
        } else {
            const char* badGw = "HTTP/1.1 502 Bad Gateway\r\nConnection: close\r\n\r\n";
            sendAll(clientFd, (const uint8_t*)badGw, strlen(badGw), 0);
            closeSocketGraceful(client);
            return;
        }
    }

    int upstreamFd = upstream.fd();
    configureSocketTimeoutsAndKeepalive(upstreamFd);

    const char* okMsg = "HTTP/1.1 200 Connection Established\r\n\r\n";
    if (!sendAll(clientFd, (const uint8_t*)okMsg, strlen(okMsg), 0)) {
        closeSocketAbort(upstream);
        closeSocketAbort(client);
        return;
    }

    uint8_t* buffer = streamPool[slotIdx];
    uint8_t* savedHello = helloPool[slotIdx];
    size_t savedHelloLen = 0;
    int retryCount = 0;

    bool isFirstPacket = true;
    bool helloPending = false;
    bool gotServerReply = false;
    bool eofFromUpstream = false;
    unsigned long helloSentMs = 0;
    unsigned long lastActMs = millis();

    while (true) {
        fd_set readFds;
        FD_ZERO(&readFds);
        FD_SET(clientFd, &readFds);
        FD_SET(upstreamFd, &readFds);
        int maxFd = (clientFd > upstreamFd ? clientFd : upstreamFd) + 1;

        uint32_t fastLimit = constrain(emaTtfbMs * 10, 800UL, 1400UL);
        uint32_t idleLimit = (uxSemaphoreGetCount(clientSlots) == 0) ? 10000UL : 90000UL;
        uint32_t waitTimeoutMs = helloPending
                                 ? ((activeStrat == 4) ? 3200UL : fastLimit)
                                 : 1000UL;

        struct timeval tv;
        tv.tv_sec = waitTimeoutMs / 1000;
        tv.tv_usec = (waitTimeoutMs % 1000) * 1000;

        int sel = select(maxFd, &readFds, NULL, NULL, &tv);
        if (sel == 0) {
            if (helloPending) {
                logPrintf("[TIMEOUT %lums] %s (%s)", (unsigned long)waitTimeoutMs, host.c_str(), targetIp.toString().c_str());
                activeStrat = reportHostFailure(host, activeStrat, useAltGfeIp);

                if (savedHelloLen > 0 && retryCount < 2) {
                    retryCount++;
                    closeSocketAbort(upstream);
                    if (useAltGfeIp && isGoogleFrontEndHost(host)) targetIp = lastWorkingGfeIp;
                    if (upstream.connect(targetIp, port, 2500)) {
                        upstreamFd = upstream.fd();
                        configureSocketTimeoutsAndKeepalive(upstreamFd);
                        helloSentMs = millis();
                        lastActMs = millis();
                        if (executeClientHelloBypass(upstreamFd, savedHello, savedHelloLen, activeStrat, host.c_str(), targetIp)) {
                            continue;
                        }
                    }
                }
            } else if (millis() - lastActMs < idleLimit) {
                continue;
            }
            break;
        }
        if (sel < 0) break;

        if (FD_ISSET(clientFd, &readFds)) {
            int len = recv(clientFd, buffer, STREAM_BUF_SIZE, 0);
            if (len <= 0) break;
            lastActMs = millis();

            if (isFirstPacket) {
                isFirstPacket = false;
                if (len >= 5 && buffer[0] == 0x16 && buffer[1] == 0x03) {
                    size_t recLen = ((size_t)buffer[3] << 8) | buffer[4];
                    size_t totalExpected = 5 + recLen;
                    unsigned long t0 = millis();

                    while ((size_t)len < totalExpected && totalExpected <= STREAM_BUF_SIZE && millis() - t0 < 250) {
                        fd_set rfd;
                        FD_ZERO(&rfd);
                        FD_SET(clientFd, &rfd);
                        struct timeval stv = { 0, 20000 };
                        if (select(clientFd + 1, &rfd, NULL, NULL, &stv) > 0) {
                            int more = recv(clientFd, buffer + len, totalExpected - (size_t)len, 0);
                            if (more <= 0) break;
                            len += more;
                        }
                    }

                    if ((size_t)len == totalExpected && len >= 64) {
                        if ((size_t)len <= HELLO_BUF_SIZE) {
                            memcpy(savedHello, buffer, len);
                            savedHelloLen = (size_t)len;
                        }
                        helloPending = true;
                        helloSentMs = millis();
                        if (!executeClientHelloBypass(upstreamFd, buffer, (size_t)len, activeStrat, host.c_str(), targetIp)) {
                            logPrintf("[SEND ERR] %s errno=%d", host.c_str(), errno);
                            break;
                        }
                        continue;
                    }
                }
            }

            if (!sendAll(upstreamFd, buffer, (size_t)len, 0)) break;
        }

        if (FD_ISSET(upstreamFd, &readFds)) {
            int len = recv(upstreamFd, buffer, STREAM_BUF_SIZE, 0);
            if (len <= 0) {
                eofFromUpstream = true;
                if (helloPending) {
                    logPrintf("[RST/EOF %lums] %s (%s)", millis() - helloSentMs, host.c_str(), targetIp.toString().c_str());
                    activeStrat = reportHostFailure(host, activeStrat, useAltGfeIp);

                    if (savedHelloLen > 0 && retryCount < 2) {
                        retryCount++;
                        closeSocketAbort(upstream);
                        if (useAltGfeIp && isGoogleFrontEndHost(host)) targetIp = lastWorkingGfeIp;
                        if (upstream.connect(targetIp, port, 2500)) {
                            upstreamFd = upstream.fd();
                            configureSocketTimeoutsAndKeepalive(upstreamFd);
                            helloSentMs = millis();
                            lastActMs = millis();
                            if (executeClientHelloBypass(upstreamFd, savedHello, savedHelloLen, activeStrat, host.c_str(), targetIp)) {
                                continue;
                            }
                        }
                    }
                }
                break;
            }

            lastActMs = millis();

            if (!gotServerReply) {
                gotServerReply = true;
                if (helloPending) {
                    helloPending = false;
                    savedHelloLen = 0;
                    unsigned long ttfb = millis() - helloSentMs;
                    logPrintf("[OK %lums] %s (%s dns=%lums) rx=%db",
                              ttfb, host.c_str(), targetIp.toString().c_str(), dnsMs, len);
                    reportHostSuccess(host, activeStrat, targetIp, ttfb);
                }
            }

            if (!sendAll(clientFd, buffer, (size_t)len, 0)) break;
        }
    }

    if (gotServerReply) {
        if (eofFromUpstream) upstream.stop(); else closeSocketAbort(upstream);
        closeSocketGraceful(client);
    } else {
        closeSocketAbort(upstream);
        closeSocketAbort(client);
    }
}

struct TaskContext {
    WiFiClient* client;
    int slotIdx;
};

void proxyTask(void* param) {
    TaskContext* ctx = (TaskContext*)param;
    WiFiClient* clientPtr = ctx->client;
    int slotIdx = ctx->slotIdx;
    delete ctx;

    runProxySession(*clientPtr, slotIdx);

    delete clientPtr;
    releaseSlotIndex(slotIdx);

    uint32_t watermark = (uint32_t)uxTaskGetStackHighWaterMark(NULL);
    if (watermark < minStackFreeBytes) {
        minStackFreeBytes = watermark;
        if (watermark < 1024) {
            logPrintf("[WARN] Low stack watermark: %u bytes", (unsigned)watermark);
        }
    }

    xSemaphoreGive(clientSlots);
    vTaskDelete(NULL);
}

void setup() {
    #if ARDUINO_USB_CDC_ON_BOOT
      Serial0.begin(115200);
      Serial.begin(115200);
    #else
      Serial.begin(115200);
    #endif
    delay(500);

    logMutex = xSemaphoreCreateMutex();
    cacheMutex = xSemaphoreCreateMutex();
    dnsMutex = xSemaphoreCreateMutex();
    slotMaskMutex = xSemaphoreCreateMutex();
    clientSlots = xSemaphoreCreateCounting(MAX_CLIENTS, MAX_CLIENTS);

    memset(hostCache, 0, sizeof(hostCache));
    memset(dnsCache, 0, sizeof(dnsCache));
    memset(logs, 0, sizeof(logs));
    memset(slotInUse, 0, sizeof(slotInUse));

    for (int i = 0; i < MAX_CLIENTS; i++) {
        streamPool[i] = (uint8_t*)(psramFound() ? ps_malloc(STREAM_BUF_SIZE) : malloc(STREAM_BUF_SIZE));
        helloPool[i]  = (uint8_t*)(psramFound() ? ps_malloc(HELLO_BUF_SIZE)  : malloc(HELLO_BUF_SIZE));
    }

    csrfToken = esp_random();
    if (csrfToken == 0) csrfToken = 0x5A33C1F9;

    esp_err_t ret = nvs_flash_init();
    if (ret == ESP_ERR_NVS_NO_FREE_PAGES || ret == ESP_ERR_NVS_NEW_VERSION_FOUND) {
        nvs_flash_erase();
        nvs_flash_init();
    }
    loadCacheFromNvs();

    logPrintf("sdkconfig: SOCK=%d ACT_TCP=%d LISTEN=%d MSL=%d WND=%d SND=%d",
              CONFIG_LWIP_MAX_SOCKETS, CONFIG_LWIP_MAX_ACTIVE_TCP, CONFIG_LWIP_MAX_LISTENING_TCP,
              CONFIG_LWIP_TCP_MSL, CONFIG_LWIP_TCP_WND_DEFAULT, CONFIG_LWIP_TCP_SND_BUF_DEFAULT);

    WiFi.onEvent([](arduino_event_id_t, arduino_event_info_t) {
        applyCleanDns();
    }, ARDUINO_EVENT_WIFI_STA_GOT_IP);

    WiFi.mode(WIFI_STA);
    WiFi.config(STATIC_IP, GATEWAY_IP, SUBNET_MASK, DNS_SERVER_1, DNS_SERVER_2);
    WiFi.setSleep(false);
    WiFi.setAutoReconnect(true);
    WiFi.begin(WIFI_SSID, WIFI_PASSWORD);

    while (WiFi.status() != WL_CONNECTED) {
        delay(500);
    }

    esp_wifi_set_ps(WIFI_PS_NONE);
    applyCleanDns();

    if (mdns_init() == ESP_OK) {
        mdns_hostname_set("esp32s3");
        mdns_instance_name_set("ESP32-S3 YouTube AntiDPI");
    }

    #if defined(ESP_ARDUINO_VERSION_MAJOR) && ESP_ARDUINO_VERSION_MAJOR >= 3
      esp_task_wdt_config_t wdtCfg = {
          .timeout_ms = 15000,
          .idle_core_mask = 0,
          .trigger_panic = true
      };
      esp_task_wdt_reconfigure(&wdtCfg);
    #else
      esp_task_wdt_init(15, true);
    #endif
    esp_task_wdt_add(NULL);

    logPrintf("Wi-Fi OK! IP: %s:%u | SRAM: %uKB | PSRAM: %uKB",
              WiFi.localIP().toString().c_str(), PROXY_PORT,
              (unsigned)(ESP.getFreeHeap() / 1024), (unsigned)(ESP.getFreePsram() / 1024));

    proxyServer.begin();
    proxyServer.setNoDelay(true);
}

unsigned long lastWifiCheckMs = 0;

void loop() {
    esp_task_wdt_reset();

    unsigned long saveInterval = initialNvsSaved ? NVS_SAVE_INTERVAL_MS : 30000UL;
    if (nvsForceSave || (nvsDirty && millis() - lastNvsSaveMs > saveInterval)) {
        saveCacheToNvs();
        logPrintf("=== Saved cache to NVS ===");
    }

    if (millis() - lastWifiCheckMs > 10000) {
        lastWifiCheckMs = millis();
        if (WiFi.status() != WL_CONNECTED) {
            WiFi.reconnect();
        }
    }

    if (uxSemaphoreGetCount(clientSlots) > 0) {
        WiFiClient newClient = proxyServer.available();
        if (newClient) {
            if (xSemaphoreTake(clientSlots, 0) == pdTRUE) {
                int slotIdx = acquireSlotIndex();
                if (slotIdx >= 0 && streamPool[slotIdx] && helloPool[slotIdx]) {
                    TaskContext* ctx = new TaskContext{ new WiFiClient(newClient), slotIdx };
                    if (xTaskCreatePinnedToCore(proxyTask, "proxy", 8192, ctx, 1, NULL, 1) != pdPASS) {
                        delete ctx->client;
                        delete ctx;
                        releaseSlotIndex(slotIdx);
                        closeSocketAbort(newClient);
                        xSemaphoreGive(clientSlots);
                    }
                } else {
                    if (slotIdx >= 0) releaseSlotIndex(slotIdx);
                    closeSocketAbort(newClient);
                    xSemaphoreGive(clientSlots);
                }
            } else {
                closeSocketAbort(newClient);
            }
        }
    }

    vTaskDelay(2 / portTICK_PERIOD_MS);
}