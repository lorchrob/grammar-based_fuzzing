#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_LINE_LENGTH 1024

//!! ISSUES
/*
  1. Only subbing in dns_domain_name_output, not other outputs
  2. Getting garbage from dns_domain_name_output, e.g. lines that are only a single paren
*/

int main() {
    FILE *dns_base_file, *domain_name_file, *output_file;
    char *line1, line2[MAX_LINE_LENGTH], *modified_line;

    dns_base_file = fopen("results/dns_base_output.txt", "r");
    domain_name_file = fopen("results/dns_domain_name_output.txt", "r");

    output_file = fopen("results/dns_combined.txt", "w");

    if (dns_base_file == NULL || domain_name_file == NULL || output_file == NULL) {
        perror("Error opening files");
        return 1;
    }

    // Read dns_base_file line by line
    size_t line1_size = MAX_LINE_LENGTH;
    line1 = (char *)malloc(line1_size);

    while (fgets(line1, line1_size, dns_base_file) != NULL) {
        // Check if the line contains "LabelListStub"
        char *match_position = strstr(line1, "LabelListStub");

        

        if (match_position != NULL) {
            // Read the corresponding line from domain_name_file
            if (fgets(line2, sizeof(line2), domain_name_file) != NULL) {

                if (strlen(line2) > 0 && line2[strlen(line2) - 1] == '\n') {
                    line2[strlen(line2) - 1] = '\0';
                }

                  size_t modified_line_length = strlen(line1) - strlen("LabelListStub") + strlen(line2) + 1;
                  modified_line = (char *)malloc(modified_line_length);

                  snprintf(modified_line, modified_line_length, "%.*s%s%s",
                          (int)(match_position - line1), line1, line2, match_position + strlen("LabelListStub"));

                  free(line1);
                  line1 = modified_line;
            } else {
                // Handle case where domain_name_file is shorter than dns_base_file
                break;
            }
        }

        fputs(line1, output_file);

        // Resize line1 if needed
        if (strlen(line1) == line1_size - 1 && line1[line1_size - 2] != '\n') {
            line1_size *= 2;
            line1 = (char *)realloc(line1, line1_size);
        }
    }

    fclose(dns_base_file);
    fclose(domain_name_file);
    fclose(output_file);

    return 0;
}
