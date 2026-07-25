# Docker Compose Files

This directory contains Docker Compose configurations for testing and development.

## Usage

Since the docker-compose files are in `config/`, you need to use the `-f` flag:

```bash
# Standard compose file
docker-compose -f config/docker-compose.yml up

# Test compose file
docker-compose -f config/docker-compose.test.yml up

# Or create an alias for convenience
alias dc='docker-compose -f config/docker-compose.yml'
alias dct='docker-compose -f config/docker-compose.test.yml'
```

## Files

- `docker-compose.yml` - Main development environment
- `docker-compose.test.yml` - Test isolation environment
- `*.sdn` - Configuration files for Simple Language tools
