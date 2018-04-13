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

#include "Error.h"
#include "SAT_glucose.h"
#include "Util.h"

#include <algorithm>
#include <cassert>

using namespace std;

namespace SAT {

  enum {TIMEOUT, UNSATISFIABLE, SATISFIABLE};

  GlucoseView::GlucoseView(Manager & _man, Expr::Manager::View & _eview) :
    View(_man, _eview), incremental_enabled(false)
  {
  }

  GlucoseView::~GlucoseView() {
  }

  bool GlucoseView::add(Clause & clause, GID gid) throw(Trivial) {

    View::cleanClause(clause);

    Glucose::vec<Glucose::Lit> lits(clause.size());
    int i = 0;
    for (Clause::iterator it = clause.begin(); it != clause.end(); ++i, it++) {
      ID v = *it;
      bool pos = true;
      if (exprView.op(v) != Expr::Var) {
        int _n;
        const ID * const _args = exprView.arguments(v, &_n);
        v = _args[0];
        pos = false;
      }
      VMap::iterator mapIt = vmap.find(v);
      if (mapIt == vmap.end()) {
        Glucose::Var vi = satMan.newVar();
        pair<VMap::iterator, bool> rv = vmap.insert(VMap::value_type(v, vi));
        mapIt = rv.first;
        ivmap.insert(IVMap::value_type(vi, v));
      }
      Glucose::Var sv = mapIt->second;
      lits[i] = Glucose::mkLit(sv, !pos);
    }
    if(gid != NULL_GID)
      lits.push(~(*(Glucose::Lit *) gid));
    satMan.addClause(lits);
    return true;
  }

  GID GlucoseView::newGID() {
    Glucose::Var v =  satMan.newVar();
    Glucose::Lit act = Glucose::mkLit(v, false);
    //Add the variable to the list of assumptions
    pair<set<Glucose::Lit>::iterator, bool> ret = _assumps.insert(act);
    assert(ret.second);
    return &(*(ret.first));
  }

  void GlucoseView::remove(GID gid) {
    Glucose::Lit gidLit = *(Glucose::Lit *) gid;
    //Remove the activation literal from the assumptions
    _assumps.erase(gidLit);
    //Add a unit clause permanently
    satMan.addClause(~gidLit);
  }

  bool GlucoseView::sat(Expr::IDVector * assump, Assignment * asgn,
                          Expr::IDVector * crits, GID, bool,
                          Assignment * lift, std::vector<Clause> *,
                          int * decision_budget)
  {
    if(incremental_enabled) {
      satMan.setIncrementalMode();
    }

    Glucose::vec<Glucose::Lit> assumps;
    for(set<Glucose::Lit>::const_iterator it = _assumps.begin();
        it != _assumps.end(); ++it) {
      assumps.push(*it);
    }
    if (assump != NULL) {
      //Add the user provided assumptions to the list of assumptions
      for(vector<ID>::const_iterator it = assump->begin(); it != assump->end();
          ++it) {
        ID v = *it;
        bool pos = true;
        if (exprView.op(v) != Expr::Var) {
          int _n;
          const ID * const _args = exprView.arguments(v, &_n);
          v = _args[0];
          pos = false;
        }
        VMap::iterator vit = vmap.find(v);
        Glucose::Var mv;
        if(vit != vmap.end()) {
          mv = vit->second;
        }
        else {
          mv = satMan.newVar();
          vmap.insert(VMap::value_type(v, mv));
          ivmap.insert(IVMap::value_type(mv, v));
        }
        assumps.push(Glucose::mkLit(mv, !pos));
      }
    }

    bool result = false;
    int64_t stime = View::tt() ? Util::get_thread_cpu_time() : 0;
    Glucose::lbool ret;
    int64_t decisions = 0;
    int64_t decisions_before = satMan.decisions;

    if (decision_budget) {
      int64_t budget = (int64_t) *decision_budget;
      assert(budget > 0);
      satMan.setDecisionBudget(budget);
      ret = satMan.solveLimited(assumps);
      satMan.budgetOff();
      decisions = satMan.decisions - decisions_before;
      *decision_budget = decisions;
    } else {
      ret = satMan.solveLimited(assumps);
    }

    int status;
    if(ret == l_True)
      status = SATISFIABLE;
    else if(ret == l_False)
      status = UNSATISFIABLE;
    else
      status = TIMEOUT;
    int64_t etime = View::tt() ? Util::get_thread_cpu_time() : 0;
    View::satTime() += (etime - stime);
    View::satCount()++;
    if (status == UNSATISFIABLE) {
      if (crits != NULL) {
        Expr::IDVector ua;
        const Glucose::vec<Glucose::Lit> & conf = satMan.conflict;
        for (int i = 0; i < conf.size(); ++i) {
          Glucose::Var var = Glucose::var(conf[i]);
          bool neg = Glucose::sign(conf[i]);
          IVMap::iterator it = ivmap.find(var);
          //it is possible that the variable has no corresponding ID which is
          //the case when it is an activation literal
          if(it != ivmap.end()) {
            ID exprVar = it->second;
            //Flip the polarity of the literal since it is coming from the
            //conflict clause
            ua.push_back(neg ? exprVar : exprView.apply(Expr::Not, exprVar));
          }
        }
        sort(crits->begin(), crits->end());
        sort(ua.begin(), ua.end());
        Expr::IDVector::iterator cit = crits->begin(), uit = ua.begin();
        while (cit != crits->end() && uit != ua.end())
          if (*cit < *uit)
            crits->erase(cit);
          else if (*cit == *uit) {
            cit++; uit++;
          }
          else
            uit++;
        if (cit != crits->end())
          crits->erase(cit, crits->end());
      }
    }
    else if (status == SATISFIABLE) {
      result = true;
      if (asgn != NULL) {
        for (Assignment::iterator it = asgn->begin(); it != asgn->end(); it++) {
          VMap::const_iterator vit = vmap.find(it->first);
          if (vit != vmap.end()) {
            Glucose::lbool va = satMan.modelValue(vit->second);
            if (va == l_False)
              it->second = False;
            else if (va == l_True)
              it->second = True;
            else
              it->second = Unknown;
          }
          else
            it->second = Unknown;
        }
      }
      if (lift != NULL) {
        *lift = *asgn;
      }
    }
    else {
      if (decision_budget) {
        result = true;
        assert(decisions >= *decision_budget);
        *decision_budget = decisions + 1;
      } else {
        throw Timeout("SAT timed out");
      }
    }

    return result;
  }

  void GlucoseView::timeout(double to) {
    if(to < 0)
      return;
    satMan.setConfBudget(to * 10000);
  }

  void GlucoseView::lockInModel() {
    satMan.initNbInitialVars(satMan.nVars());
    incremental_enabled = true;
  }
}
