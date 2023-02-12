#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <regex.h>

#define IPV6_ADDR_LEN 16 /* définit la longueur d'une adresse IPV6*/
#define IPV6_REGEX "([[:xdigit:]]{1,4}:){7}[[:xdigit:]]{1,4}" /*expression pour valider une adresse IPV6 */

bool is_valid_ipv6_address(const char *addr) {
    int status;
    regex_t regex;

    /* Vérifie que l'adresse a une longueur valide */
    if (strlen(addr) != IPV6_ADDR_LEN * 2 + 7) {
        return false;
    }

    /* Vérifie que l'adresse est formatée correctement */

    if (strncmp(addr, "::", 2) == 0) {
        addr += 2;
    }
    if (strncmp(addr, ":", 1) == 0 || strncmp(addr + strlen(addr) - 1, ":", 1) == 0) {
        return false;
    }
    if (strstr(addr, ":::") != NULL) {
        return false;
    }
    if (strstr(addr, "::") != NULL && strstr(addr, "::") != addr && strstr(addr, "::") != addr + strlen(addr) - 2) {
        return false;
    }
    if (strstr(addr, "::") == addr && strstr(addr, "::") != addr + 1) {
        return false;
    }
    if (strstr(addr, "::") == addr + strlen(addr) - 2 && strstr(addr, "::") != addr + strlen(addr) - 3) {
        return false;
    }

    /* Vérifie que l'adresse utilise des bits de préfixe valides */

    if ((unsigned char)addr[0] == 0xfe && ((unsigned char)addr[1] & 0xc0) == 0x80) {
        return false;
    }
    if ((unsigned char)addr[0] == 0xff && ((unsigned char)addr[1] & 0x10) == 0x10) {
        return false;
    }
    if (((unsigned char)addr[0] & 0xf0) == 0xf0 || ((unsigned char)addr[0] & 0xfe) == 0xfc) {
        return false;
    }

    /* Vérifie que l'adresse est conforme à la syntaxe IPv6 */
    
    if (regcomp(&regex, IPV6_REGEX, REG_EXTENDED)) {
        return false;
    }
    status = regexec(&regex, addr, 0, NULL, 0);
    regfree(&regex);
    if (status != 0) {
        return false;
    }

    return true;
}


/* Exemple d'utilisation */
int main() {
    unsigned char addr[IPV6_ADDR_LEN] = { 0x20, 0x01, 0x0d, 0xb8, 0x85, 0xa3, 0x08, 0x01,
                                          0x0d, 0xb8, 0x85, 0xa3, 0x00, 0x00, 0x00, 0x01 };
    if (is_valid_ipv6_address((const char*) addr)) {
        printf("L'adresse IPv6 est valide.\n");
    } else {
        printf("L'adresse IPv6 est invalide.\n");
    }
    return 0;
}