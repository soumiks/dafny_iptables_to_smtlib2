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
    # Add GOPATH/bin to PATH for this script execution if needed, though usually handled by user env
    export PATH=$PATH:$(go env GOPATH)/bin
fi

echo "Building Dafny project to Go..."

# 1. Transpile Dafny to Go
# This creates a 'dafny-iptables-go' directory with the Go source
dafny build --target:go src/IptablesToSmt.dfy --output:dafny-iptables-go

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
