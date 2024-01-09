#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_LINE_LENGTH 1024

int main() {
  FILE *dns_base_file, *domain_name_file, *rdata_file, *ttl_file, *output_file;
  char *line1, line2[MAX_LINE_LENGTH], *modified_line;

  dns_base_file = fopen("results/dns_base_output.txt", "r");
  domain_name_file = fopen("results/dns_domain_name_output.txt", "r");
  rdata_file = fopen("results/dns_rdata_output.txt", "r");
  ttl_file = fopen("results/dns_ttl_output.txt", "r");
  output_file = fopen("results/dns_combined.txt", "w");

  if (dns_base_file == NULL || domain_name_file == NULL ||
      output_file == NULL) {
    perror("Error opening files");
    return 1;
  }

  line1 = (char *)malloc(MAX_LINE_LENGTH);

  while (fgets(line1, MAX_LINE_LENGTH, dns_base_file) != NULL) {
    char *match_position;
    while ((match_position = strstr(line1, "LabelListStub")) != NULL) {
      if (fgets(line2, sizeof(line2), domain_name_file) != NULL) {
        if (strlen(line2) > 0 && line2[strlen(line2) - 1] == '\n') {
          line2[strlen(line2) - 1] = '\0';
        }

        size_t modified_line_length =
            strlen(line1) - strlen("LabelListStub") + strlen(line2) + 1;
        modified_line = (char *)malloc(modified_line_length);

        snprintf(modified_line, modified_line_length, "%.*s%s%s",
                 (int)(match_position - line1), line1, line2,
                 match_position + strlen("LabelListStub"));

        free(line1);
        line1 = modified_line;
      } else {
        // Handle case where domain_name_file is shorter than dns_base_file
        goto end_loops;
      }
    }

    // Check if the line contains "RDataStub"
    while ((match_position = strstr(line1, "RDataStub")) != NULL) {
      if (fgets(line2, sizeof(line2), rdata_file) != NULL) {
        if (strlen(line2) > 0 && line2[strlen(line2) - 1] == '\n') {
          line2[strlen(line2) - 1] = '\0';
        }

        size_t modified_line_length =
            strlen(line1) - strlen("RDataStub") + strlen(line2) + 1;
        modified_line = (char *)malloc(modified_line_length);

        snprintf(modified_line, modified_line_length, "%.*s%s%s",
                 (int)(match_position - line1), line1, line2,
                 match_position + strlen("RDataStub"));

        free(line1);
        line1 = modified_line;
      } else {
        // Handle case where rdata_file is shorter than dns_base_file
        goto end_loops;
      }
    }

    // Check if the line contains "TtlStub"
    while ((match_position = strstr(line1, "TtlStub")) != NULL) {
      if (fgets(line2, sizeof(line2), ttl_file) != NULL) {
        if (strlen(line2) > 0 && line2[strlen(line2) - 1] == '\n') {
          line2[strlen(line2) - 1] = '\0';
        }

        size_t modified_line_length =
            strlen(line1) - strlen("TtlStub") + strlen(line2) + 1;
        modified_line = (char *)malloc(modified_line_length);

        snprintf(modified_line, modified_line_length, "%.*s%s%s",
                 (int)(match_position - line1), line1, line2,
                 match_position + strlen("TtlStub"));

        free(line1);
        line1 = modified_line;
      } else {
        // Handle case where ttl_file is shorter than dns_base_file
        goto end_loops;
      }
    }

    fputs(line1, output_file);
  }

end_loops:

  fclose(dns_base_file);
  fclose(domain_name_file);
  fclose(output_file);
  fclose(ttl_file);

  return 0;
}
