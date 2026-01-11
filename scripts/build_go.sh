#!/bin/bash
set -e

# Default output name
OUTPUT_NAME="dafny-iptables"

# Check for required tools
if ! command -v dafny &> /dev/null; then
    echo "Error: dafny is not installed or not in PATH."
    exit 1
fi

if ! command -v go &> /dev/null; then
    echo "Error: go is not installed or not in PATH."
    exit 1
fi

# Ensure goimports is installed (Dafny's Go backend often needs it)
if ! command -v goimports &> /dev/null; then
    echo "Warning: goimports not found. Installing..."
    go install golang.org/x/tools/cmd/goimports@latest
fi

# Add GOPATH/bin to PATH so Dafny can find goimports
export PATH=$PATH:$(go env GOPATH)/bin

echo "Building Dafny project to Go..."

# Clean up previous build artifacts
rm -rf dafny-iptables-go

# 1. Transpile Dafny to Go
# --output:dafny-iptables will create 'dafny-iptables-go' directory
dafny build --target:go src/IptablesToSmt.dfy --output:dafny-iptables

# 2. Build the final Go binary
echo "Compiling Go binary..."
# Dafny generates code that expects a GOPATH structure (src/PackageName),
# so we set GOPATH to the generated directory.
export GOPATH=$(pwd)/dafny-iptables-go
export GO111MODULE=off

cd dafny-iptables-go/src

# Build the binary
go build -o ../../$OUTPUT_NAME dafny-iptables.go

cd ../..

echo "Build successful! Executable created at: ./$OUTPUT_NAME"
