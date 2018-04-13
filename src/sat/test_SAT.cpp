/********************************************************************
Copyright (c) 2010-2015, Regents of the University of Colorado

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

Neither the name of the University of Colorado nor the names of its
contributors may be used to endorse or promote products derived from
this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.
********************************************************************/

#include "Expr.h"
#include "ExprUtil.h"

#include "SAT.h"

#include <cassert>
#include <iostream>
#include <vector>
#include <algorithm>

using namespace std;

void helper_check_asgn(Expr::Manager::View * v, SAT::Assignment * asgn, vector<int>& expected)
{
    cout<<"Assignment:"<<endl;
    int i = 0;
    for (SAT::Assignment::iterator it = asgn->begin(); it != asgn->end(); it++, i++) {
        cout << stringOf(*v, it->first) << " " << it->second << endl;
        assert (it->second == expected[i]);
    }
}

void test1(Expr::Manager::View * v, SAT::Manager * sman, SAT::Manager::View * sview)
{
    cout<<"Running "<<__func__<<endl;
    SAT::Clause ca, cb, cc;
    ID a = v->newVar("a");
    ID b = v->newVar("b");
    ID c = v->newVar("c");

    ca.push_back(a);
    ca.push_back(v->apply(Expr::Not, b));

    cb.push_back(b);
    cb.push_back(v->apply(Expr::Not, c));

    cc.push_back(c);

    // global constraints on globally visible variables
    sman->add(ca);
    sman->add(cb);
    sman->add(cc);

    Expr::IDVector assumps;
    assumps.push_back(v->apply(Expr::Not, a));
    assumps.push_back(v->apply(Expr::Not, b));

    // only care about values for these variables
    SAT::Assignment asgn;
    asgn.insert(SAT::Assignment::value_type(a, SAT::Unknown));
    asgn.insert(SAT::Assignment::value_type(b, SAT::Unknown));
    asgn.insert(SAT::Assignment::value_type(c, SAT::Unknown));

    // assumps is shrunk to a core of lits
    bool rv = sview->sat(&assumps, NULL, &assumps);
    cout << "sat with all assumps: " << rv <<endl;
    cout << assumps.size() <<endl;
    assert (!rv);

    // which should be sufficient to still yield unsat
    rv = sview->sat(&assumps, NULL, &assumps);
    cout << "sat with core assumps: " << rv << endl;
    cout << assumps.size() << endl;
    assert (!rv);

    // but w/o the assumps, it's sat
    rv = sview->sat(NULL, &asgn, NULL);
    assert (rv);
    cout << "sat without assumps: " << rv << endl;
    for (SAT::Assignment::iterator it = asgn.begin(); it != asgn.end(); it++) {
        cout << stringOf(*v, it->first) << " " << it->second << endl;
        assert (it->second == SAT::True);
    }
}

void test2(Expr::Manager::View * v, SAT::Manager * sman, SAT::Manager::View * sview)
{
    cout<<"Running "<<__func__<<endl;
    SAT::Clause ca, cb, cc;
    ID a = v->newVar("a");
    ID b = v->newVar("b");
    ID c = v->newVar("c");

    ca.push_back(a);
    ca.push_back(b);
    ca.push_back(c);

    cb.push_back(v->apply(Expr::Not, b));
    cb.push_back(c);
    
    cc.push_back(v->apply(Expr::Not, c));

    // global constraints on globally visible variables
    sman->add(ca);
    sman->add(cb);
    sman->add(cc);
    
    Expr::IDVector assumps;
    assumps.push_back(v->apply(Expr::Not, a));
    assumps.push_back(v->apply(Expr::Not, c));

    // only care about values for these variables
    SAT::Assignment asgn;
    asgn.insert(SAT::Assignment::value_type(a, SAT::Unknown));
    asgn.insert(SAT::Assignment::value_type(b, SAT::Unknown));
    asgn.insert(SAT::Assignment::value_type(c, SAT::Unknown));

    bool rv = sview->sat(NULL, &asgn, NULL);
    cout << "sat: " << rv << endl;
    assert (rv);

    vector<int> expected = {SAT::False, SAT::False, SAT::True};
    helper_check_asgn(v, &asgn, expected);
    
    //now try with assumps
    rv = sview->sat(&assumps, &asgn, &assumps);
    cout << "sat with assumps: " << rv << endl;
    assert (!rv);
    for (Expr::IDVector::iterator it = assumps.begin(); it!=assumps.end(); it++){
        cout<<"crit "<<stringOf(*v, *it)<<endl;
    }
}

void test3(Expr::Manager::View * v, SAT::Manager * sman, SAT::Manager::View * sview)
{
    cout<<"Running "<<__func__<<endl;
    SAT::Clause ca, cb, cc, ce, cd;
    ID a = v->newVar("a");
    ID b = v->newVar("b");
    ID c = v->newVar("c");  

    ca.push_back(a);
    ca.push_back(b);
    ca.push_back(c);

    cb.push_back(v->apply(Expr::Not, a));
    cc.push_back(v->apply(Expr::Not, b));
    cd.push_back(v->apply(Expr::Not, c));
    ce.push_back(a);

    // global constraints on globally visible variables
    sman->add(ca);
    sman->add(cb);
    sman->add(cc);
    sman->add(cd);
    sman->add(ce);

    // only care about values for these variables
    SAT::Assignment asgn;
    asgn.insert(SAT::Assignment::value_type(a, SAT::Unknown));
    asgn.insert(SAT::Assignment::value_type(b, SAT::Unknown));
    asgn.insert(SAT::Assignment::value_type(c, SAT::Unknown));

    bool rv = sview->sat(NULL, &asgn, NULL);
    cout << "sat: " << rv << endl;    
    assert (!rv);
}

void test4(Expr::Manager::View * v, SAT::Manager * sman, SAT::Manager::View * sview)
{
    cout<<"Running "<<__func__<<endl;
    SAT::Clause ca, cb, cc;
    ID a = v->newVar("a");
    ID b = v->newVar("b");
    ID c = v->newVar("c");  
    ID d = v->newVar("d");  

    ca.push_back(a);
    ca.push_back(b);
    ca.push_back(v->apply(Expr::Not, c));

    cb.push_back(c);
    cb.push_back(d);
    
    cc.push_back(v->apply(Expr::Not, a));
    cc.push_back(v->apply(Expr::Not, b));

    // global constraints on globally visible variables
    sman->add(ca);
    sman->add(cb);
    sman->add(cc);
    
    Expr::IDVector assumps;
    assumps.push_back(v->apply(Expr::Not, d));
    assumps.push_back(v->apply(Expr::Not, a));

    // only care about values for these variables
    SAT::Assignment asgn;
    asgn.insert(SAT::Assignment::value_type(a, SAT::Unknown));
    asgn.insert(SAT::Assignment::value_type(b, SAT::Unknown));
    asgn.insert(SAT::Assignment::value_type(c, SAT::Unknown));
    asgn.insert(SAT::Assignment::value_type(d, SAT::Unknown));

    bool rv = sview->sat(&assumps, &asgn, &assumps);
    cout << "sat: " << rv << endl;  
    assert (rv);

    vector<int> expected = {SAT::False, SAT::True, SAT::True, SAT::False};
    helper_check_asgn(v, &asgn, expected);
    
    //this assumption should make it unsat
    assumps.push_back(v->apply(Expr::Not, b));
    rv = sview->sat(&assumps, &asgn, &assumps);
    cout<<"sat: "<<rv<<endl;
    assert(!rv);
    for (Expr::IDVector::iterator it = assumps.begin(); it!=assumps.end(); it++){
    cout<<"crit "<<stringOf(*v, *it)<<endl;
    }
}

void test_groups(Expr::Manager::View * v, SAT::Manager * sman, SAT::Manager::View * sview)
{
    cout<<"Running "<<__func__<<endl;
    SAT::Clause c1, c2, c3, c4;
    ID a = v->newVar("a");
    ID b = v->newVar("b");
    ID c = v->newVar("c");  

    c1.push_back(a);
    c1.push_back(b);
    c1.push_back(c);

    c2.push_back(v->apply(Expr::Not, a));
    c3.push_back(v->apply(Expr::Not, b));
    c4.push_back(v->apply(Expr::Not, c));
    
    sman->add(c1);
    //add clauses 2-4 in a group
    SAT::GID gid = sview->newGID();
    sview->add(c2, gid);
    sview->add(c3, gid);
    sview->add(c4, gid);

    // only care about values for these variables
    SAT::Assignment asgn;
    asgn.insert(SAT::Assignment::value_type(a, SAT::Unknown));
    asgn.insert(SAT::Assignment::value_type(b, SAT::Unknown));
    asgn.insert(SAT::Assignment::value_type(c, SAT::Unknown));

    //should be unsat with all clauses
    bool rv = sview->sat(NULL, &asgn, NULL);
    cout << "sat with groups: " << rv << endl;  
    assert (!rv);

    //remove group -> remove clauses 2-4. Should be sat now
    sview->remove(gid);
    rv = sview->sat(NULL, &asgn, NULL);
    cout << "sat without groups: " << rv << endl; 
    assert(rv);
    
    //Add assumptions to set all variables to true. Should still be sat
    //if all clauses in group were removed properly
    Expr::IDVector assumps;
    assumps.push_back(a);
    assumps.push_back(b);
    assumps.push_back(c);
    
    rv = sview->sat(&assumps, &asgn, NULL);
    cout << "sat with assumps: " << rv << endl; 
    assert(rv);
    vector<int> expected = {SAT::True, SAT::True, SAT::True};
    helper_check_asgn(v, &asgn, expected);
}

void test_unsat_core(Expr::Manager::View * v, SAT::Manager * sman, SAT::Manager::View * sview)
{
    cout<<"Running "<<__func__<<endl;
    ID a = v->newVar("a");
    ID b = v->newVar("b");
    ID c = v->newVar("c");  
    ID d = v->newVar("d");  

    SAT::Clause c1, c2, c3, c4, c5, c6, c7, c8;
    c1.push_back(a);
    c1.push_back(b);
    c1.push_back(v->apply(Expr::Not, c));

    c2.push_back(v->apply(Expr::Not, a));
    c2.push_back(v->apply(Expr::Not, b));
    
    c3.push_back(a);
    c3.push_back(c);
    c3.push_back(d);
    
    c4.push_back(v->apply(Expr::Not, d));
    c4.push_back(b);
    
    c5.push_back(d);
    c5.push_back(v->apply(Expr::Not, a));
    
    c6.push_back(v->apply(Expr::Not, d));
    c6.push_back(v->apply(Expr::Not, b));
    c6.push_back(a);
    
    c7.push_back(a);
    c7.push_back(v->apply(Expr::Not, c));
    
    c8.push_back(v->apply(Expr::Not, d));

    sman->add(c1);
    sman->add(c2);
    sman->add(c3);
    sman->add(c4);
    sman->add(c5);
    sman->add(c6);
    sman->add(c7);
    sman->add(c8);

    std::vector<SAT::Clause> core;
    bool rv = sview->sat(NULL, NULL, NULL, 0, false, NULL, &core);
    cout << "sat: " << rv << endl;  
    assert (!rv);
    
    if (sview->supportsCore()) {
        std::vector<SAT::Clause> expected_vector = {c3, c5, c7, c8};

        for(auto it = expected_vector.begin(); it != expected_vector.end(); ++it) {
            std::sort(it->begin(), it->end());
        }

        for(auto it = core.begin(); it != core.end(); ++it) {
            std::sort(it->begin(), it->end());
        }

        std::set<SAT::Clause> actual(core.begin(), core.end());
        std::set<SAT::Clause> expected(expected_vector.begin(), expected_vector.end());
        // The core could be an over-aproximation, just check that is 
        // contains the expected clauses
        for (const SAT::Clause & c : expected){
            assert(actual.find(c) != actual.end());
        }
    }
}

typedef void test_func(Expr::Manager::View * v, SAT::Manager * sman, SAT::Manager::View * sview);

int main(void) {

    vector<string> backends;
    backends.push_back("minisat");
#ifndef DISABLE_ZCHAFF
    backends.push_back("zchaff");
#endif
    backends.push_back("picosat");
    backends.push_back("glucose");
  
    //vector of test functions to run
    vector<test_func*> tests;
    tests.push_back(test1);
    tests.push_back(test2);
    tests.push_back(test3);
    tests.push_back(test4);
    tests.push_back(test_groups);
    tests.push_back(test_unsat_core);
    
    for(auto it = backends.begin(); it != backends.end(); ++it) {
        string backend = *it;
        cout << "Testing backend " << backend << endl;
        
        for (auto t=tests.begin(); t != tests.end(); t++){
            Expr::Manager * man = new Expr::Manager();
            Expr::Manager::View * v = man->newView();
            SAT::Manager * sman = new SAT::Manager(*man);
            bool trace_gen = (backend == "picosat");
            SAT::Manager::View * sview = sman->newView(*v, backend, trace_gen);
            if(backend == "picosat") {
                assert(sview->supportsCore());
            } else {
                assert(!(sview->supportsCore()));
            }
            (*t)(v, sman, sview);

            delete sview;
            delete sman;
            delete v;
            delete man;
        }
    }
}
