set shell := ["bash", "-euo", "pipefail", "-c"]
set positional-arguments

# The memory cap of one build command, in systemd units; override it with GAULOIS_MAX_RAM.
max_ram := env("GAULOIS_MAX_RAM", "1536M")

# The prefix of every build command: a transient scope in the shared slice, with swap disabled.
capped := "systemd-run --user --scope --quiet --slice=gaulois.slice --property=MemoryMax=" + max_ram + " --property=MemorySwapMax=0 --"
