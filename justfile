import "just/settings.just"

# List the developer workflows.
[default]
list:
    @just --list

# Cap the total memory of the slice that every build command shares, until the next reboot.
slice-cap size="9G":
    systemctl --user set-property --runtime gaulois.slice MemoryMax="$1" MemorySwapMax=0

# Build the given dune targets, or everything when none are given.
build *targets:
    {{ capped }} dune build -j 2 "$@"

# Build the Rocq tests and examples, then run the OCaml inline tests.
test *args:
    {{ capped }} dune build -j 2 @tests/default @examples/default @runtest "$@"

# Check formatting, source hygiene, layout and kernel-reported theorem assumptions.
check *args:
    {{ capped }} bash -c 'dune build -j 2 @fmt @theories/default @examples/default @tests/default tools/gaulois.exe "$@" && exec _build/default/tools/gaulois.exe check' -- "$@"

# Format every source file in place.
fmt:
    {{ capped }} dune fmt
