#PASS: (0)
AF(win | lose | push)
#PASS: (1)
AF(state<2> & ~state<1> & state<0>)
#PASS: (2)
AG(~bad<0>)
#PASS: (3)
AG(~bad<1>)
#PASS: (4)
AG(~bad<2>)
#FAIL: (5)
AG(~bad<3>)
#PASS: (6)
AG(~bad<4>)
#PASS: (7)
AG(~bad<5>)
#PASS: (8)
AG((dScore<4> & (dScore<3> | (dScore<2> & dScore<1>))) -> AX(dScore<4> & (dScore<3> | (dScore<2> & dScore<1>))))
#PASS: (9)
AG((pScore<4> & (pScore<3> | (pScore<2> & pScore<1>))) -> AX(pScore<4> & (pScore<3> | (pScore<2> & pScore<1>))))
#PASS: (10)
AG((dScore<4> & (dScore<3> | (dScore<2> & dScore<1>))) -> AG(dScore<4> & (dScore<3> | (dScore<2> & dScore<1>))))
#PASS: (11)
AG((pScore<4> & (pScore<3> | (pScore<2> & pScore<1>))) -> AG(pScore<4> & (pScore<3> | (pScore<2> & pScore<1>))))
#PASS: (12)
AG(~bad<6>)
#PASS: (13)
AG(~bad<7>)
#PASS: (14)
AG((dScore<4> & (dScore<3> | (dScore<2> & dScore<1>))) -> AG(~lose))
#PASS: (15)
AG((pScore<4> & (pScore<3> | (pScore<2> & pScore<1>))) -> AG(~win))
#PASS: (16)
AG(~bad<8>)
#PASS: (17)
AG(~bad<9>)
#PASS: (18)
AG(~bad<10>)
#PASS: (19)
AG(~bad<11>)
#PASS: (20)
AG(~bad<12>)
#PASS: (21)
AG(~bad<13>)
#PASS: (22)
AG(~bad<14>)
#PASS: (23)
AG(~bad<15>)
#PASS: (24)
AG(~bad<16>)
#PASS: (25)
AG(~bad<17>)
#PASS: (26)
AG(~bad<18>)
#PASS: (27)
AG(~bad<19>)
#PASS: (28)
AG(~bad<20>)
#PASS: (29)
AG(~bad<21>)
#PASS: (30)
AG(~bad<22>)
#PASS: (31)
AG(~bad<23>)
#PASS: (32)
AG(~bad<24>)
#PASS: (33)
AG((~state<2> & ~state<1> & state<0>) -> AG(state<2> | state<1> | state<0>))
#PASS: (34)
AG(pAces -> AX(pAces))
#PASS: (35)
AG(dAces -> AX(dAces))
#PASS: (36)
AG(~bad<25>)
#PASS: (37)
AG(~bad<26>)
#FAIL: (38)
AG(~bad<27>)
#PASS: (39)
AG(~bad<28>)
#PASS: (40)
AG((state<2> & ~state<1>) -> AX(state<2> & ~state<1> & state<0>))
#FAIL: (41)
AG(pScore<4> & ~pScore<3> & pScore<2> & ~pScore<1> & ~pScore<0> &
   ~deck<*1*><4> & ~deck<*1*><3> & ~deck<*1*><2> & ~deck<*1*><1> &
   ~deck<*1*><0> -> AX(state<2> | ~state<1> | state<0> | AF(lose)))
#PASS: (42)
AG(pScore<4> & ~pScore<3> & pScore<2> & ~pScore<1> & ~pScore<0> &
   ~deck<*1*><4> & ~deck<*1*><3> & ~deck<*1*><2> & ~deck<*1*><1> &
   ~deck<*1*><0> -> AX(state<2> | ~state<1> | state<0> | ~valid | AF(lose)))
#PASS: (43)
AG((~pCards<3> & ~pCards<2> & pCards<1> & ~pCards<0> &
    ~dCards<3> & ~dCards<2> & ~dCards<1> & ~dCards<0>) ->
   AX (~pCards<3> & ~pCards<2> & pCards<1> & ~pCards<0>))
#PASS: (44)
AG((~dCards<3> & ~dCards<2> & dCards<1> & ~dCards<0> &
    ~pCards<3> & ~pCards<2> & pCards<1> & ~pCards<0>) -> 
   AX((~dCards<3> & ~dCards<2> & dCards<1> & ~dCards<0>) |
      (~pCards<3> & ~pCards<2> & pCards<1> & ~pCards<0>)))
#PASS: (45)
AG((pCards<1> & ~pCards<0>) -> AX(pCards<1>))
#PASS: (46)
AG((dCards<1> & ~dCards<0>) -> AX(dCards<1>))
#PASS: (47)
AF(state<2> & ~state<1> & ~state<0>)
#PASS: (48)
AG(AF(state<2> & ~state<1> & state<0>))
#FAIL: (49)
AG(AF(state<2> & ~state<1> & ~state<0>))
