#!/bin/bash

set -ex

export ASAN_OPTIONS="detect_odr_violation=0 detect_leaks=0"
export MSAN_OPTIONS="symbolize=1"

# Run address sanitizer
RUSTFLAGS="-Z sanitizer=address" \
cargo test --tests --target x86_64-unknown-linux-gnu --features memmap

# Run leak sanitizer
RUSTFLAGS="-Z sanitizer=leak" \
cargo test --tests --target x86_64-unknown-linux-gnu --features memmap

# Run memory sanitizer
RUSTFLAGS="-Z sanitizer=memory" \
cargo test --tests --target x86_64-unknown-linux-gnu --features memmap

# Run thread sanitizer
RUSTFLAGS="-Z sanitizer=thread" \
cargo -Zbuild-std=test,std --tests --target x86_64-unknown-linux-gnu --features memmap
