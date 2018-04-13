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
#include "SAT_picosat.h"
#include "Util.h"

#include <algorithm>
#include <cassert>

using namespace std;

namespace SAT {

  enum {TIMEOUT, UNSATISFIABLE, SATISFIABLE};

  PicosatView::PicosatView(Manager & _man, Expr::Manager::View & _eview, bool enable_trace_generation) :
    View(_man, _eview)
  {
    satMan = picosat_init();
    if (enable_trace_generation){
      int res = picosat_enable_trace_generation(satMan); //needed to extract cores or proof traces
      assert(res);
    }
  }

  PicosatView::~PicosatView() {
    if(satMan) {
      picosat_reset(satMan);
      satMan = NULL;
    }
  }

  bool PicosatView::add(Clause & clause, GID gid) throw(Trivial) {
    View::cleanClause(clause);

    int i = 0;
    for (Clause::iterator it = clause.begin(); it != clause.end(); ++i, it++)
    {
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
        int vi = picosat_inc_max_var(satMan); //picosat id for this variable?
        pair<VMap::iterator, bool> rv = vmap.insert(VMap::value_type(v, vi));
        mapIt = rv.first;
        ivmap.insert(IVMap::value_type(vi, v));
      }
      int sv = mapIt->second;
      picosat_add(satMan, pos ? sv : -sv); //negative indicates not
    }
    if (gid != NULL_GID){
      //add activation literal for the group
      picosat_add(satMan, -(*(int *)gid));
    }

    int clause_id = picosat_add(satMan, 0); //terminate the clause
    all_clauses[clause_id] = clause;

    return true;
  }

  GID PicosatView::newGID() {
    int gid = picosat_inc_max_var(satMan);
    pair<set<int>::iterator, bool> ret = group_assumps.insert(gid);
    assert(ret.second);
    return &(*(ret.first));
  }

  void PicosatView::remove(GID gid) {
    int theGid = *(int *) gid;
    //Add a unit clause permanently
    picosat_add(satMan, -(*(int *)gid));
    picosat_add(satMan, 0);
    //Remove the activation literal from the assumptions
    group_assumps.erase(theGid);

  }

  bool PicosatView::sat(Expr::IDVector * assump, Assignment * asgn,
      Expr::IDVector * crits, GID, bool,
      Assignment * lift, std::vector<Clause> * core,
      int * decision_budget)
  {
    if (decision_budget) {
      throw std::logic_error("PicosatView does not support decision_budget");
    }

    //activate all groups by adding assumptions for their activation literals
    for(set<int>::iterator it=group_assumps.begin(); it!=group_assumps.end(); it++){
      picosat_assume(satMan, *it);
    }

    if (assump != NULL){
      for (Expr::IDVector::iterator it = assump->begin(); it != assump->end(); it++) {
        ID v = *it;
        bool pos = true;
        if (exprView.op(v) != Expr::Var) {
          int _n;
          const ID * const _args = exprView.arguments(v, &_n);
          v = _args[0];
          pos = false;
        }
        VMap::iterator vit = vmap.find(v);
        int mv;
        if(vit != vmap.end()) {
          mv = vit->second;
        }
        else {
          mv = picosat_inc_max_var(satMan);
          vmap.insert(VMap::value_type(v, mv));
          ivmap.insert(IVMap::value_type(mv, v));
        }
        picosat_assume(satMan, pos ? mv : -mv);
      }
    }

    bool result = false;
    int ret = picosat_sat(satMan, -1); //-1 => no decision limit
    if (ret == PICOSAT_UNSATISFIABLE){
      result = false;
      if (crits != NULL){
        //check each assumption in crits and erase those which are not critical
        for (Expr::IDVector::iterator cit = crits->begin(); cit!=crits->end(); ){
          ID v = *cit;
          bool pos = true;
          if (exprView.op(v) != Expr::Var) {
            int _n;
            const ID * const _args = exprView.arguments(v, &_n);
            v = _args[0];
            pos = false;
          }
          VMap::iterator vit = vmap.find(v);
          if(vit != vmap.end()) {
            int mv = vit->second;
            int is_crit = picosat_failed_assumption(satMan, pos ? mv : -mv);
            if (!is_crit){
              crits->erase(cit);
            }
            else cit++;
          }
          else {
            //if the variable doesn't exist then it's definitely not critical so erase it
            crits->erase(cit);
          }
        }
      }
      if (core != NULL){
        for (std::unordered_map<int, Clause>::iterator it=all_clauses.begin(); it!=all_clauses.end(); it++){
          if (picosat_coreclause(satMan, it->first)){
            core->push_back(it->second);
          }
        }
      }
    }
    else if (ret == PICOSAT_SATISFIABLE){
      result = true;
      if (asgn != NULL) {
        //get satisfying assignment
        for (Assignment::iterator it = asgn->begin(); it != asgn->end(); it++) {
          VMap::const_iterator vit = vmap.find(it->first);
          if (vit != vmap.end()) {
            int va = picosat_deref(satMan, vit->second);
            if (va == -1)
              it->second = False;
            else if (va == 1)
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
    else{
      throw Timeout("SAT timed out");
    }

    return result;
  }

  void PicosatView::timeout(double to) {
    if(to < 0)
      return;

    //propagation_limit is supposed to be linearly related to time
    picosat_set_propagation_limit(satMan, to*10000);
  }
}
