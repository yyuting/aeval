#ifndef MUSOLVER__HPP__
#define MUSOLVER__HPP__
#include <assert.h>

#include "ae/SMTUtils.hpp"
#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace boost;
namespace ufo
{

  // non-recursive version (don't be confused with ExprSimpl.hpp::getConj(Expr a, ExprSet &conjs))
  static inline void getConj(Expr s, ExprVector& ops)
  {
    if (isOpX<AND>(s))
    {
      for (unsigned i = 0; i < s->arity(); i++)
      {
        ops.push_back(s->arg(i));
      }
    }
    else ops.push_back(s);
  }

  static inline bool rewrite(Expr a, Expr b, Expr& fla)
  {
    ExprVector av;
    filter (a, bind::IsConst (), inserter(av, av.begin()));

    ExprMap matching;
    if (findMatchingSubexpr (a, fla, av, matching))
    {
      Expr toRepl1 = a;
      Expr toRepl2 = b;
      {
        toRepl1 = replaceAll(toRepl1, matching);
        toRepl2 = replaceAll(toRepl2, matching);
      }
      fla = replaceAll(fla, toRepl1, toRepl2);
      return true;
    }
    return false;
  }

  inline static void mu(Expr s)
  {
    ExprFactory& efac = s->getFactory();
    SMTUtils u(efac);
    ExprVector cnjs;
    getConj(s, cnjs);

    Expr flaRel;
    Expr fla;
    Expr flaForall;
    ExprMap recDefsMu;
    ExprMap recDefsNu;
    Expr muVar;
    Expr nuVar;

    for (auto c : cnjs)
    {
      if (isOpX<FORALL>(c))
      {
        c = regularizeQF(c);
        if (isOpX<FAPP>(c->last())) flaRel = c->last();
        if (isOpX<EQ>(c->last()))
        {
          flaForall = c;
          fla = c->last();
        }
      }

      if (isOpX<AND>(c) && isOpX<FORALL>(c->right())
          && isOpX<EQ>(c->right()->last()))
      {
        Expr var = c->left();
        string pref = lexical_cast<string>(var);
        c = regularizeQF(c->right());
        if (pref == "mu")
        {
          recDefsMu[c->last()->left()] = c->last()->right();
          muVar = var;
        }
        if (pref == "nu")
        {
          recDefsNu[c->last()->left()] = c->last()->right();
          nuVar = var;
        }
      }
    }

    assert(flaRel == fla->left());

    Expr flaOrig = fla;
    bool usedNu = false;

    ExprSet flaApps;
    filter (fla, bind::IsFApp (), inserter(flaApps, flaApps.begin()));
    for (auto & app : flaApps)
    {
      Expr appRepled = app;
      for (auto & a : recDefsMu)
        rewrite(a.first, a.second, appRepled);

      for (auto & a : recDefsNu)
        usedNu |= rewrite(a.first, a.second, appRepled);

      fla = replaceAll(fla, app, appRepled);
    }

    fla = expandExists(fla);
    fla = simplifyExists(fla);
    
    // creating abstraction

    ExprSet dsj;
    getDisj(fla->right(), dsj);
    ExprSet newDisj;

    for (auto & d : dsj)
    {
      ExprSet cnj;
      getConj(d, cnj);
      Expr app;
      for (auto & c : cnj)
      {
        for (auto & a : recDefsMu)
          if (contains(c, a.first->left()))
            app = c;
        for (auto & a : recDefsNu)
          if (contains(c, a.first->left()))
            app = c;
      }
      if (app == NULL) app = conjoin(cnj, efac);
      getDisj(app, newDisj);
    }

    fla = disjoin(newDisj, efac);

    // finding matching

    ExprSet flaOrigDisj;
    getDisj(flaOrig->right(), flaOrigDisj);

    Expr ex1;
    Expr ex2;
    Expr used;
    ExprMap matching;

    assert(flaOrigDisj.size() == 2); // GF: to extend

    for (auto & a : flaOrigDisj)
    {
      ExprVector av;
      filter (a, bind::IsConst (), inserter(av, av.begin()));
      bool toBreak = false;

      if (isOpX<EXISTS>(a)) continue;

      for (auto & d : newDisj)
      {
        if (isOpX<EXISTS>(d)) continue;
        matching.clear();
        if (findMatchingSubexpr (a, d, av, matching))
        {
          used = d;
          toBreak = true;
          break;
        }
      }
      if (toBreak) break;
    }

    for (auto & a : flaOrigDisj)
    {
      if (isOpX<EXISTS>(a))
      {
        ex1 = a;
        break;
      }
    }
    for (auto & d : newDisj)
    {
      if (isOpX<EXISTS>(d))
      {
        ex2 = d;
        break;
      }
    }

    // validate exist
    if (!matching.empty() && ex1 != NULL && ex2 != NULL && existEqual(replaceAll(ex1, matching), ex2))
    {
      Expr upd = replaceAll(flaRel, matching);
      newDisj.erase(ex2);
      newDisj.erase(used);
      newDisj.insert(upd);
      fla = replaceAll(flaForall, flaForall->last(), mk<EQ>(flaOrig->left(), disjoin(newDisj, efac)));
      if (usedNu) fla = mk<AND>(nuVar, fla);
        else fla = mk<AND>(muVar, fla);
      u.serialize_formula(fla);
    }
  };
}

#endif
