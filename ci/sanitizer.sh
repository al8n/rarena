#!/bin/bash

set -ex

export ASAN_OPTIONS="detect_odr_violation=0 detect_leaks=0"

# Run address sanitizer
RUSTFLAGS="-Z sanitizer=address" \
cargo test --tests --target x86_64-unknown-linux-gnu --features memmap

# Run leak sanitizer
RUSTFLAGS="-Z sanitizer=leak" \
cargo test --tests --target x86_64-unknown-linux-gnu --features memmap

# Run memory sanitizer
RUSTFLAGS="-Z -Zsanitizer=memory -Zsanitizer-memory-track-origins" \
# RUSTDOCFLAGS="-Zsanitizer=memory -Zsanitizer-memory-track-origins" \ 
cargo test --tests --target x86_64-unknown-linux-gnu --features memmap

# Run thread sanitizer
RUSTFLAGS="-Z sanitizer=thread" \
cargo -Zbuild-std=test,std --tests --target x86_64-unknown-linux-gnu --features memmap
