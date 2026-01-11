
Dafny program verifier finished with 20 verified, 0 errors
(set-logic ALL)
(declare-const packet_chain String)
(declare-const packet_src String)
(declare-const packet_dst String)
(declare-const packet_proto String)
(declare-const packet_sport String)
(declare-const packet_dport String)
(declare-const packet_action String)
(assert (distinct packet_chain ""))

; Rule 0 (line 8): -A INPUT -s 10.0.0.0/8 -p tcp -j ACCEPT
(define-fun rule0 ((pkt_chain String) (pkt_src String) (pkt_dst String) (pkt_proto String) (pkt_sport String) (pkt_dport String)) Bool
  (and
    (= pkt_chain "INPUT")
    (= pkt_src "10.0.0.0/8")
    (= pkt_proto "tcp")
  )
)
(assert (=> (rule0 packet_chain packet_src packet_dst packet_proto packet_sport packet_dport)
            (= packet_action "ACCEPT")))

; Rule 1 (line 10): -A INPUT -p tcp --dport 23 -j DROP
(define-fun rule1 ((pkt_chain String) (pkt_src String) (pkt_dst String) (pkt_proto String) (pkt_sport String) (pkt_dport String)) Bool
  (and
    (= pkt_chain "INPUT")
    (= pkt_proto "tcp")
    (= pkt_dport "23")
  )
)
(assert (=> (rule1 packet_chain packet_src packet_dst packet_proto packet_sport packet_dport)
            (= packet_action "DROP")))

; Rule 2 (line 12): -A OUTPUT -d 203.0.113.53/32 -p udp -j ACCEPT
(define-fun rule2 ((pkt_chain String) (pkt_src String) (pkt_dst String) (pkt_proto String) (pkt_sport String) (pkt_dport String)) Bool
  (and
    (= pkt_chain "OUTPUT")
    (= pkt_dst "203.0.113.53/32")
    (= pkt_proto "udp")
  )
)
(assert (=> (rule2 packet_chain packet_src packet_dst packet_proto packet_sport packet_dport)
            (= packet_action "ACCEPT")))

; Rule 3 (line 14): -A OUTPUT -d 198.51.100.42/32 -j REJECT
(define-fun rule3 ((pkt_chain String) (pkt_src String) (pkt_dst String) (pkt_proto String) (pkt_sport String) (pkt_dport String)) Bool
  (and
    (= pkt_chain "OUTPUT")
    (= pkt_dst "198.51.100.42/32")
  )
)
(assert (=> (rule3 packet_chain packet_src packet_dst packet_proto packet_sport packet_dport)
            (= packet_action "REJECT")))

