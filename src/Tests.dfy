include "IptablesToSmt.dfy"

module Tests {
  import opened IptablesToSmt

  // SECTION 1: This test should PASS because ParseTarget has strong specs.
  method TestParseTarget() {
    var t1 := ParseTarget("DROP");
    assert t1 == TargetDrop;

    var t2 := ParseTarget("ACCEPT");
    assert t2 == TargetAccept;

    var t3 := ParseTarget("MyChain");
    assert t3 == TargetJump("MyChain");
  }

  // SECTION 2: This test should now PASS because ParseRuleTokens has strong specs.
  method TestParseRule_Pass() {
    // Input: "-A INPUT -s 1.2.3.4 -j ACCEPT"
    var tokens := ["-A", "INPUT", "-s", "1.2.3.4", "-j", "ACCEPT"];
    var idx := 1;
    var raw := "-A INPUT -s 1.2.3.4 -j ACCEPT";
    
    // We expect: Rule(chain="INPUT", source=MatchExact("1.2.3.4"), target=TargetAccept ...)
    var r, ok := ParseRuleTokens(tokens, idx, raw);
    
    // Help the prover unroll the recursive search:
    var t2 := tokens[2..]; // ["-s", "...", "-j", "..."]
    assert t2[0] == "-s"; 
    // FindMatch(t2) recurses to FindMatch(t2[1..])
    assert t2[1..][0] == "1.2.3.4";
    // Recurses to t2[2..] which starts with "-j"
    assert t2[2..][0] == "-j";
    // Match found!
    
    assert FindMatch(tokens[2..], "-j").MatchExact?;
    
    assert ok; 
    assert r.chain == "INPUT"; 
    // Now verifiable!
    assert r.source == MatchExact("1.2.3.4"); 
    assert r.target == TargetAccept;
  }
}
