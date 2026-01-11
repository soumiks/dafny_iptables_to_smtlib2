# dafny_iptables_to_smtlib2

A formally verified Dafny program that parses a subset of the `iptables-save` format and emits an SMT-LIB 2.0 encoding. This ensures that the translation from firewall rules to logical assertions is mathematically correct.

## Features

- **Formally Verified Parser**: The input parser is verified against strong functional specifications. We prove that the `Rule` object returned exactly matches the input tokens.
- **Verified Output Generation**: The SMT-LIB printer is verified to produce safe, non-empty, and structurally correct output.
- **Unit Proofs**: Instead of runtime unit tests, this project uses compile-time "Unit Proofs" (`src/Tests.dfy`) which guarantee correctness for specific inputs mathematically.
- **Precondition Propagation**: The codebase explicitly handles preconditions (like "no carriage returns") from the core logic all the way to the `Main` entry point.

## Running the translator

1. **Install Dafny**: Ensure you have Dafny 4.0+ installed.
2. **Run on a file**:

   ```bash
   dafny run src/IptablesToSmt.dfy -- "$(cat samples/iptables-sample.rules)" > rules.smt2
   ```

   The tool reads the entire input as a single string argument.

## Building with Go

To build a standalone executable using the Go backend:

```bash
./scripts/build_go.sh
```

This will produce a `dafny-iptables` binary in the project root. You can run it like this:

```bash
./dafny-iptables -- "$(cat samples/iptables-sample.rules)" > rules.smt2
```

## Verification

To verified the correctness of the parser and printer:

```bash
dafny run src/Tests.dfy
```

This will run the suite of Unit Proofs. A successful run (exit code 0) means the code is mathematically proven to satisfy its specifications.

## Project Structure

- `src/IptablesToSmt.dfy`: Main application code, fully specified with `requires` and `ensures`.
- `src/Tests.dfy`: The suite of Unit Proofs that acts as the constraint verification layer.
- `samples/`: Sample iptables dump files.

## Modeling Details

- **Supported Flags**: `-s`, `-d`, `-p`, `--sport`, `--dport`, `-j`.
- **Targets**: `ACCEPT`, `DROP`, `REJECT`, `RETURN` are modeled explicitly. Others are generic jumps.
- **Logic**: Each `-A` rule is translated into a function `(define-fun ruleN ...)` and an assertion `(assert (=> (ruleN ...) action))`.

## License

MIT
