# dafny_iptables

This repository contains a small Dafny program that parses a subset of the `iptables-save` format and emits an SMT-LIB encoding that can be consumed by Z3. Each `-A` rule is translated into a function that checks whether a symbolic packet matches the rule and asserts the resulting target action.

## Running the translator

1. Install the Dafny toolchain (version 4.0 or newer) so the `dafny` CLI is available in your `$PATH`.
2. Capture an `iptables-save` dump in a file, e.g. `iptables-save > rules.txt`.
3. Run the translator and redirect its output to an SMT-LIB file. Choose one of the following approaches:

```bash
cd /Users/soumik/code/dafny_iptables
# Option A: pass the dump as a single quoted argument (preserves newlines).
dafny run src/IptablesToSmt.dfy -- "$(cat rules.txt)" > rules.smt2

# Option B: let the helper script read the file and invoke Dafny for you.
./scripts/iptables_to_smt.sh rules.txt > rules.smt2
```

The resulting `rules.smt2` file declares symbolic packet fields (`packet_chain`, `packet_src`, `packet_dst`, `packet_proto`, `packet_action`) and contains one rule definition per `-A` entry. You can now load this SMT-LIB script with Z3 or another solver to explore reachability of actions.

## Sample data

The `samples/iptables-sample.rules` file contains a short, self-contained `iptables-save` dump that exercises the translator. Try it out without touching your host firewall rules:

```bash
dafny run src/IptablesToSmt.dfy -- "$(cat samples/iptables-sample.rules)" > sample.smt2
```

Open `sample.smt2` to inspect the generated solver constraints.

## Notes

- Only a handful of flags are understood today: `-s`, `-d`, `-p`, and `-j`. Unrecognized modifiers are ignored but preserved in comments via the original rule text.
- Targets other than `ACCEPT`, `DROP`, `REJECT`, or `RETURN` are modeled as opaque jumps (`TargetJump`).
- The entry point expects the entire `iptables-save` listing as its last argument when launched via `dafny run`. When running from a shell, wrap `$(cat file)` in quotes (as shown above) so that line breaks are preserved in the argument string.
- Extend `ParseRuleTokens` and `BuildRuleConditions` if you need additional match modules or to incorporate counters and policies.
