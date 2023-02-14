#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <regex.h>


#define IPV6_ADDR_LEN 16 /* définit la longueur d'une adresse IPV6*/
#define IPV6_REGEX "([[:xdigit:]]{1,4}:){7}[[:xdigit:]]{1,4}" /*expression pour valider une adresse IPV6 */

/*@ ghost char * current_str; */

/*@ ghost bool current_status; */

/*@
  requires \valid(regex);
  requires \valid(pattern+(0..strlen(pattern)));
  requires \valid(cflags);
  assigns \nothing;
  behavior error:
    assumes regcomp(regex, pattern, cflags) != 0;
    assigns \nothing;
    ensures \result == -1;
  behavior success:
    assumes regcomp(regex, pattern, cflags) == 0;
    assigns \nothing;
    ensures \result == 0;
*/


extern int regcomp(regex_t *restrict regex, const char *restrict pattern, int cflags);

/*@
  requires \valid(regex);
  assigns \nothing;
  behavior free:
    assumes regfree(regex) == 0;
    assigns \nothing;
    ensures \result == 0;
*/

extern void regfree(regex_t *regex);

/*@
  requires \valid(addr+(0..strlen(addr)));
  assigns \nothing;
  behavior not_valid:
    assumes strlen(addr) != IPV6_ADDR_LEN * 2 + 7;
    assigns \nothing;
    ensures \result == false;
  behavior valid:
    assumes strlen(addr) == IPV6_ADDR_LEN * 2 + 7;
    assigns current_str, current_status;
    ensures current_str == addr;
    ensures current_status == \result;
*/

bool is_valid_ipv6_address(const char *addr) {
    int status;
    regex_t regex;

/*@ assert valid_string(addr);
  @*/
  
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

    char addr2[IPV6_ADDR_LEN*2+7] = "2001:0db8:85a3:0000:0000:8a2e:0370:7334";
    if (is_valid_ipv6_address(addr2)) {
        printf("L'adresse IPv6 2 est valide.\n");
    } else {
        printf("L'adresse IPv6 2 est invalide.\n");
    }

    char addr3[IPV6_ADDR_LEN*2+7] = "2001:db8:85a3::8a2e:0370:7334";
    if (is_valid_ipv6_address(addr3)) {
        printf("L'adresse IPv6 3 est valide.\n");
    } else {
        printf("L'adresse IPv6 3 est invalide.\n");
    }

    char addr4[IPV6_ADDR_LEN*2+7] = "2001:0db8:0000:0000:0000:ff00:0042:8329";
    if (is_valid_ipv6_address(addr4)) {
        printf("L'adresse IPv6 4 est valide.\n");
    } else {
        printf("L'adresse IPv6 4 est invalide.\n");
    }

    char addr5[IPV6_ADDR_LEN*2+7] = "2001:db8::ff00:42:8329";
    if (is_valid_ipv6_address(addr5)) {
        printf("L'adresse IPv6 5 est valide.\n");
    } else {
        printf("L'adresse IPv6 5 est invalide.\n");
    }

    char addr6[IPV6_ADDR_LEN*2+7] = "2001:db8:abcd::123";
    if (is_valid_ipv6_address(addr6)) {
        printf("L'adresse IPv6 6 est valide.\n");
    } else {
        printf("L'adresse IPv6 6 est invalide.\n");
    }
}