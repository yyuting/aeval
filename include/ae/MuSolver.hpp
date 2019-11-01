#ifndef MUSOLVER__HPP__
#define MUSOLVER__HPP__
#include <assert.h>

#include "ae/SMTUtils.hpp"
#include "ae/AeValSolver.hpp"
#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace boost;
namespace ufo
{
  class MuSolver
  {
    private:
      Expr flaMain;
      Expr flaRel;
      Expr fla;
      Expr flaForall;
      Expr flaOrig;
      ExprSet flaOrigDisj;
      ExprMap recDefsMu;
      ExprMap recDefsNu;
      Expr muVar;
      Expr nuVar;
      ExprFactory& efac;
      SMTUtils u;
      bool usedNu;

    public:
      MuSolver(ExprFactory& _efac): efac(_efac), u(_efac) {}

    // non-recursive version (don't be confused with ExprSimpl.hpp::getConj(Expr a, ExprSet &conjs))
    static inline void getConjV(Expr s, ExprVector& ops)
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

    void print(Expr & fla)
    {
      if (usedNu) fla = mk<AND>(nuVar, fla);
      else fla = mk<AND>(muVar, fla);

      // serialize everything:
      // outs () << "(declare-fun mu () Bool)\n(declare-fun nu () Bool)\n";
      u.serialize_formula(flaMain);
      u.serialize_formula(simplifyArithm(fla));
    }

    void initialize(Expr s)
    {
      ExprFactory& efac = s->getFactory();
      ExprVector cnjs;
      getConjV(s, cnjs);

      for (auto c : cnjs)
      {
        if (isOpX<FORALL>(c))
        {
          c = regularizeQF(c);
          if (isOpX<FAPP>(c->last()))
          {
            flaMain = c;
            flaRel = c->last();
          }
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
            Expr def = c->last()->right();
            for (auto & a : recDefsNu)
              if (contains (def, a.first)) exit(0);
            recDefsMu[c->last()->left()] = def;
            muVar = var;
          }
          if (pref == "nu")
          {
            Expr def = c->last()->right();
            for (auto & a : recDefsMu)
              if (contains (def, a.first)) exit(0);
            recDefsNu[c->last()->left()] = def;
            nuVar = var;
          }
        }
      }

      assert(flaRel == fla->left());

      usedNu = false;
      flaOrig = fla;
      fla = fla->right();
      getDisj(flaOrig->right(), flaOrigDisj);
    }

    bool iter()
    {
      SMTUtils u(efac);

      fla = normalizeArithm(fla);
      ExprSet flaApps;
      filter (fla, bind::IsFApp (), inserter(flaApps, flaApps.begin()));
      for (auto & app : flaApps)
      {
        Expr appRepled = app;
        bool repled = false; // should not allow replacing same app more than once
        for (auto & a : recDefsMu)
          if (!repled) repled = rewrite(a.first, a.second, appRepled);

        for (auto & a : recDefsNu)
        {
          if (!repled) repled = rewrite(a.first, a.second, appRepled);
          usedNu |= repled;
        }

        fla = replaceAll(fla, app, appRepled);
      }

      fla = expandExists(fla);
      fla = simplifyExists(fla);
      fla = expandConjSubexpr(fla);

      ExprSet flaUpdDisj;
      getDisj(fla, flaUpdDisj);

      Expr ex1;
      Expr ex2;
      ExprSet used;
      ExprMap forallMatching;
      bool hasFapps = false;

      map <Expr, ExprVector> all;
      map <Expr, ExprVector> usedTmp;
      for (auto & a : flaOrigDisj)
      {
        for (auto & b : flaUpdDisj)
        {
          ExprSet tmp;
          getConj(b, tmp);
          for (auto it = tmp.begin(); it != tmp.end();)
          {
            if ((isOpX<EXISTS>(a) && isOpX<EXISTS>(*it)) ||
                (isOpX<FAPP>(a) && isOpX<FAPP>(*it) && a->left() == (*it)->left()))
            {
              it = tmp.erase(it);
              all[a].push_back(conjoin(tmp, efac));
              usedTmp[a].push_back(b);
            }
            else ++it;
          }
        }
      }

      ExprVector commonSubset;
      bool first = true;
      for (auto & a : all)
      {
        if (first) {
          first = false;
          commonSubset = a.second;
          continue;
        }

        for (auto it = commonSubset.begin(); it != commonSubset.end();)
        {
          if (find(a.second.begin(), a.second.end(), *it) == a.second.end())
            it = commonSubset.erase(it);
          else ++it;
        }
      }

      Expr comm = conjoin(commonSubset, efac);
      ExprSet toSearchRem;
      Expr matchNeedToBeFound;

      if (isOpX<TRUE>(comm))
      {
        // try to simplify further
        fla = resolve(fla);
        flaUpdDisj.clear();
        getDisj(fla, flaUpdDisj);
      }
      else
      {
        ExprSet finl;
        for (auto & a : all)
        {
          ExprVector tmp = a.second;
          bool found = false;
          for (auto & b : tmp)
          {
            if (b == comm)
            {
              found = true;
              for (auto & c : usedTmp[a.first])
              {
                if (contains(c, comm))
                {
                  flaUpdDisj.erase(c);
                  finl.insert(simplifyBool(replaceAll(c, comm, mk<TRUE>(efac))));
                }
              }
            }
          }
        }

        if (!u.implies(mkNeg(comm), disjoin(flaUpdDisj, efac)))
        {
          //outs () << "unable to create abstraction\n";
          return false;
        }

        toSearchRem = flaUpdDisj;
        flaUpdDisj = finl;
      }

      // finding forallMatching
      for (auto it = flaUpdDisj.begin(); it != flaUpdDisj.end();)
      {
        if (isOpX<EXISTS>(*it))
        {
          if (ex2 != NULL) exit(0); // unsupported
          ex2 = *it;
          it = flaUpdDisj.erase(it);
        }
        else ++it;
      }

      for (int i = 0; i < 2; i++) // try scanning two times (sometimes it's hard to find matches)
        for (auto it = flaOrigDisj.begin(); it != flaOrigDisj.end();)
        {
          if (!isOpX<FAPP>(*it))
          {
            if (isOpX<EXISTS>(*it))
            {
              ex1 = *it;
              it = flaOrigDisj.erase(it);
            }
            else ++it;
            continue;
          }
          hasFapps = true;
          ExprVector av;
          filter (*it, bind::IsConst (), inserter(av, av.begin()));
          Expr a = normalizeArithm(replaceAll(*it, forallMatching));

          bool found = false;
          for (auto it2 = flaUpdDisj.begin(); it2 != flaUpdDisj.end();)
          {
            if (!isOpX<FAPP>(*it2))
            {
              ++it2;
              continue;
            }
            Expr d = normalizeArithm(*it2);
            ExprMap matching1;
            if (findMatchingSubexpr (a, d, av, matching1))
            {
              for (auto & m : matching1)
              {
                if (m.first!=NULL && m.second != NULL && forallMatching[m.first] == NULL )
                {
                  forallMatching[m.first] = m.second;
                }
              }
              used.insert(*it2);
              it2 = flaUpdDisj.erase(it2);
              found = true;
              break;
            }
            ++it2;
          }
          if (found) it = flaOrigDisj.erase(it);
          else ++it;
        }

      if (!forallMatching.empty() && ex1 == NULL && ex2 == NULL)
      {
        bool sanityCheck = false;
        for (auto & m : forallMatching)
          if (m.first != NULL && m.second != NULL)
          {
            sanityCheck = true;
          }
        if (!sanityCheck) return false;

        if (!flaOrigDisj.empty() && !toSearchRem.empty())
        {
          Expr whatsLeft = replaceAll(disjoin(flaOrigDisj, efac), forallMatching);
          if (!u.implies(whatsLeft, disjoin(toSearchRem, efac))) return false;
          flaUpdDisj.clear();
        }

        if (isOpX<TRUE>(comm))
        {
          fla = replaceAll(flaForall, flaForall->last(),
                           mk<EQ>(flaOrig->left(),  replaceAll(flaRel, forallMatching)));
        }
        else
        {
          fla = replaceAll(flaForall, flaForall->last(),
                           mk<EQ>(flaOrig->left(), mk<OR>(mkNeg(comm),
                                  mk<AND>(comm, replaceAll(flaRel, forallMatching)))));
        }
        print(fla);
        return true;
      }

      // validate exist
      if ((!forallMatching.empty() || !hasFapps) && ex1 != NULL && ex2 != NULL)
      {
        ExprVector av;
        if (hasFapps)
        {
          for (unsigned i = 0; i < ex1->arity() - 1; i++)
            av.push_back(bind::fapp(ex1->arg(i)));
        }
        else
        {
          filter (ex1->last(), bind::IsConst (), inserter(av, av.begin()));
        }

        ex1 = replaceAll(ex1, forallMatching);
        ex2 = normalizeArithm(ex2);

        ExprSet cnjs1, cnjs2;
        getConj(ex1->last(), cnjs1);
        getConj(ex2->last(), cnjs2);
        if (!flaOrigDisj.empty()) cnjs1.insert(disjoin(flaOrigDisj, efac));
        if (!toSearchRem.empty()) cnjs2.insert(disjoin(toSearchRem, efac));

        ExprMap existsMatching;
        for (auto it1 = cnjs1.begin(); it1 != cnjs1.end(); )
        {
          bool doBreak = false;
          for (auto it2 = cnjs2.begin(); it2 != cnjs2.end(); )
          {
            ExprMap m1 = existsMatching;
            if (findMatchingSubexpr (*it1, *it2, av, m1))
            {
              existsMatching = m1;
              it1 = cnjs1.erase(it1);
              it2 = cnjs2.erase(it2);
              doBreak = true;
              break;
            }
            else ++it2;
          }
          if (!doBreak) ++it1;
        }

        for (auto & m : existsMatching)
          if (m.first != NULL && m.second != NULL)
          {

            Expr tmp = cloneVar(m.first, mkTerm<std::string> (lexical_cast<string>(m.first)+"_tmp", efac));
            Expr tmp1 = mk<EQ>(tmp, m.second);
            ExprSet v;
            filter (m.second, bind::IsConst (), inserter(v, v.begin()));
            AeValSolver ae(mk<TRUE>(efac), tmp1, v, false, false);
            if (ae.solve())
            {
              outs() << "  Surjectivity sanity failed: " << *m.first << "  <-->  " << *m.second << "\n";
              exit(0);
            }
          }

        Expr whatsLeft = replaceAll(conjoin(cnjs1, efac), existsMatching);
        Expr match = conjoin(cnjs2, efac);
        if (u.implies(match, whatsLeft))
        {
          // currently, an incomplete search here
          if (cnjs1.empty()) // that is, whatsLeft == true
          {
            // do nothing
          }
          else if (u.implies(match, whatsLeft))
          {
            flaUpdDisj.clear();
          }
          else
          {
            // TODO: find a subset of "match" that is equivalent to whatsLeft and remove
          }

          Expr upd = replaceAll(replaceAll(flaRel, forallMatching), existsMatching);
          flaUpdDisj.insert(upd);
          if (isOpX<TRUE>(comm))
          {
            fla = replaceAll(flaForall, flaForall->last(), mk<EQ>(flaOrig->left(),
                        disjoin(flaUpdDisj, efac)));
          } else {
            fla = replaceAll(flaForall, flaForall->last(), mk<EQ>(flaOrig->left(),
                        mk<OR>(mkNeg(comm), mk<AND>(comm, disjoin(flaUpdDisj, efac)))));
          }
          print(fla);
          return true;
        }
      }

      return false;
    };
  };

  inline static void mu (Expr s)
  {
    MuSolver m(s->getFactory());
    m.initialize(s);
    for (int i = 0; i < 2; i++) if (m.iter()) break;
  }
}

#endif
