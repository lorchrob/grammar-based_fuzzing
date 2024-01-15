import socket
import struct
import random

def build_dns_query(domain):
  # DNS header
  transaction_id = random.randint(1, 65535)
  flags = 0x0100  # Standard query
  questions = 1

  header = struct.pack('!HHHHHH', transaction_id, flags, questions, 0, 0, 0)

  # DNS question section
  qname = b''.join(struct.pack('!B', len(label)) + label.encode() for label in domain.split('.'))
  question = qname + struct.pack('!HH', 0, 1)  # QTYPE=A, QCLASS=IN

  return header + question

def send_dns_query(query_packet):
  # Configure the local caching resolver address
  resolver_address = ('8.8.8.8', 53)

  # Create a UDP socket
  with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s:
    # Send the DNS query
    s.sendto(query_packet, resolver_address)

    # Receive the response
    response, _ = s.recvfrom(1024)

  return response

def parse_dns_response(response):
  # Parse the DNS response
  transaction_id, flags, questions, answers, _, _ = struct.unpack('!HHHHHH', response[:12])

  print(f"Transaction ID: {transaction_id}")
  print(f"Flags: {flags}")
  print(f"Questions: {questions}")
  print(f"Answers: {answers}")

if __name__ == "__main__":
  domain_to_query = "example.com"  # Replace with the domain you want to query

  # Build DNS query packet
  dns_query_packet = build_dns_query(domain_to_query)

  # Send DNS query and receive response
  dns_response = send_dns_query(dns_query_packet)

  # Parse DNS response
  parse_dns_response(dns_response)

