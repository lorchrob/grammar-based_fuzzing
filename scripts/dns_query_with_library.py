import dns.resolver

def query_local_resolver(domain):
  resolver = dns.resolver.Resolver(configure=False)

  # Use the local BIND caching resolver (replace with the actual IP if necessary)
  resolver.nameservers = ['127.0.0.1']

  try:
      result = resolver.resolve(domain)
      for answer in result:
          print(answer)
  except dns.exception.DNSException as e:
      print(f"Error: {e}")

if __name__ == "__main__":
  domain_to_query = "example.com"  # Replace with the domain you want to query
  query_local_resolver(domain_to_query)
