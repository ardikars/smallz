#!/bin/bash

# Exit on error
set -e

# Get project name from Cargo.toml
PROJECT_NAME=$(grep '^name' Cargo.toml | head -1 | sed -E 's/name\s*=\s*"([^"]+)"/\1/')

echo "Cleaning build artifacts for project: $PROJECT_NAME"

# Define paths
TARGET_DIR="target/debug"

# Remove only project's compiled artifacts
rm -rf \
  "$TARGET_DIR/deps/${PROJECT_NAME}-"* \
  "$TARGET_DIR/build/${PROJECT_NAME}-"* \
  "$TARGET_DIR/.fingerprint/${PROJECT_NAME}-"* \
  "$TARGET_DIR/incremental" \
	"$TARGET_DIR/coverage"

echo "Project-only clean complete."

rustup component add llvm-tools-preview
export RUSTFLAGS="-Cinstrument-coverage"
export CARGO_INCREMENTAL=0
export LLVM_PROFILE_FILE="xdc-%p-%m.profraw"
cargo test
# cargo test --target=powerpc-unknown-linux-gnu
grcov . -s . --binary-path $TARGET_DIR -t html --branch --ignore-not-existing -o $TARGET_DIR/coverage/
find . -type f -name '*.profraw' -exec rm {} +
