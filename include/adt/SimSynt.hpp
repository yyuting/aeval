#ifndef SIMSYNT__HPP__
#define SIMSYNT__HPP__

#include "adt/ADTSolver.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  class SimSynt
  {
    private:

    ExprFactory &efac;
    SMTUtils u;
    ExprVector &ops1;
    ExprVector &ops2;

    public:

    SimSynt(ExprFactory& _efac, ExprVector& _ops1, ExprVector& _ops2) :
      efac(_efac), u(_efac), ops1(_ops1), ops2(_ops2) {}

    Expr baseCon;
    Expr indCon;
    ExprSet allSubformulas;
    ExprMap varVersions;
    ExprMap varVersions1;

    void checkConstructor(Expr op, ExprVector& constructors, bool& base, bool& ind)
    {
      base = false;
      ind = false;
      for (auto & c : constructors)
      {
        Expr capp;
        if (isOpX<EQ>(op))
        {
          Expr lhs = op->left();
          Expr rhs = op->right();
          if (isOpX<FAPP>(rhs) && rhs->left() == c) capp = rhs;
          else if (isOpX<FAPP>(lhs) && lhs->left() == c) capp = lhs;
        }
        if (capp != NULL)
        {
          for (int j = 0; j < c->arity() - 1; j++)
          if (c->last() == c->arg(j))
          {
            // first comes first serve here (to be generalized)
            if (indCon == NULL) indCon = capp;
            ind = true;
            break;
          }
          if (!ind)
          {
            // first comes firts serve here (to be generalized)
            if (baseCon == NULL) baseCon = capp;
            base = true;
            break;
          }
        }
      }
    }

    void proc(ExprVector& constructors)
    {
      assert(ops1.size() == ops2.size());

      Expr baseFormula1, baseFormula2;
      for (int i = 0; i < ops1.size(); i++)
      {
        bool base1, ind1, base2, ind2;
        checkConstructor(ops1[i], constructors, base1, ind1);
        checkConstructor(ops2[i], constructors, base2, ind2);
        if (base1 || base2)
        {
          if (base1)
          {
            baseFormula1 = ops1[i];
            baseFormula2 = ops2[i];
          }
          else
          {
            baseFormula1 = ops2[i];
            baseFormula2 = ops1[i];
          }
        }
        else
        {
          getConj(rewriteSelectStore(ops1[i]), allSubformulas);
          getConj(rewriteSelectStore(ops2[i]), allSubformulas);
        }
      }

      if (allSubformulas.size() == 0)
      {
        outs () << "Unable to proceed\n";
        return;
      }

      ExprSet vars;
      ExprVector argsPrimed;
      ExprVector types;
      filter(conjoin(ops1, efac), bind::IsConst (), inserter(vars, vars.begin()));
      filter(conjoin(ops2, efac), bind::IsConst (), inserter(vars, vars.begin()));
      for (auto & v : vars)
      {
        string str = lexical_cast<string>(v);
        if (str.back() == '1')
        {
          str.pop_back();
          for (auto & v1 : vars)
          {
            if (str == lexical_cast<string>(v1))
            {
              varVersions[v] = v1;
              varVersions1[v1] = v;
              break;
            }
          }
          argsPrimed.push_back(v);
          types.push_back(bind::typeOf(v));
        }
      }

      types.push_back (mk<BOOL_TY> (efac));
      Expr rel = bind::fdecl (mkTerm<string> ("R", efac), types);

      assert(isOpX<EQ>(baseFormula1));

      ExprVector argsBase;
      ExprVector argsInd1;
      ExprVector argsInd2;

      for (auto & v : argsPrimed)
      {
        if (contains(baseFormula1, varVersions[v]))
        {
          argsBase.push_back(baseCon);
        }
        else
        {
          if (varVersions[v] == NULL)
          {
            outs () << "NO UNPRIMED VAR FOR " << *v <<"\n";
            return;
          }
          argsBase.push_back(varVersions[v]);
        }
        argsInd1.push_back(v);                // primed
        if (isOpX<AD_TY>(v->last()->last()))
          argsInd2.push_back(v);   // unprimed
        else
          argsInd2.push_back(varVersions[v]);
      }

      Expr baseApp = bind::fapp (rel, argsBase);
      Expr baseEq = mk<EQ>(baseApp, baseFormula2);

      // serialize base case
      ExprSet baseVars;
      ExprVector baseArgs;
      filter(baseEq, bind::IsConst (), inserter(baseVars, baseVars.begin()));
      for (auto & a : baseVars) if (a != baseCon) baseArgs.push_back(a->last());
      baseArgs.push_back(baseEq);
      Expr baseRelation = mknary<FORALL>(baseArgs);
      u.serialize_formula(baseRelation);

      ExprSet otherConstraints;
      map <Expr, ExprVector> tmp;
      for (auto & f : allSubformulas)
      {
        bool found = false;
        for (auto & var : argsInd1)
        {
          if (contains(f, var))
          {
            if (isOpX<EQ>(f))
            {
              if (var == f->left())
              {
                tmp[var].push_back(f->right());
                found = true;
              }
              else if (var == f->right())
              {
                tmp[var].push_back(f->left());
                found = true;
              }
            }
          }
        }
        if (!found) otherConstraints.insert(f);
      }

      for (int adtVar = 0; adtVar < argsInd2.size(); adtVar++)
      {
        Expr var = argsInd2[adtVar];
        // identify the only ADT-argument here
        if(tmp[var].size() > 0)
        {
          auto args = argsInd2;
          // tmp[var] contains (possibly many) constructors of the ADT
          for (auto & a : tmp[var])
          {
            // compile LHS of the equality
            args[adtVar] = a;
            Expr indApp2 = bind::fapp (rel, args);

            ExprSet vrs;
            filter (a, bind::IsConst (), inserter(vrs, vrs.begin()));

            int arrVar = -1;
            for (int j = 0; j < argsInd2.size(); j++)
            {
              if (isOpX<ARRAY_TY>(argsInd2[j]->last()->last()))
                arrVar = j;
            }

            int intVar = -1;
            for (int j = 0; j < argsInd2.size(); j++)
            {
              if (isOpX<INT_TY>(argsInd2[j]->last()->last()))
              {
                if (intVar == -1) // hack right now (to try other index variables)
                  intVar = j;
              }
            }

            // guess RHS of the equality
            if (arrVar >= 0 && intVar >= 0)
            {
              ExprSet cnjs;
              for (auto & c : otherConstraints)
              {
                if (contains(c, argsInd2[intVar]) && !containsOp<AD_TY>(c) && !containsOp<ARRAY_TY>(c))
                  cnjs.insert(c);
              }
              for (auto & vr : vrs)
              {
                if (vr->last()->last() == argsInd2[arrVar]->last()->last()->last())
                {
                  for (auto e : tmp[varVersions1[argsInd2[intVar]]])
                  {
                    if (isOpX<PLUS>(e)) e = mk<MINUS>(e->left(), e->right()); // hack right now
                    ExprSet cnjs1 = cnjs;
                    cnjs1.insert(mk<EQ>(vr, mk<SELECT>(argsInd2[arrVar], e)));
                    ExprVector args2 = argsInd2;
                    args2[intVar] = e;
                    args2[adtVar] = varVersions[args2[adtVar]];
                    cnjs1.insert(bind::fapp (rel, args2));

                    ExprVector args1;
                    ExprVector vars;

                    filter(indApp2, bind::IsConst (), inserter(vars, vars.begin()));
                    for (auto & a : vars)
                    {
                      if (a != baseCon) args1.push_back(a->last());
                    }
                    args1.push_back(mk<EQ>(indApp2, conjoin(cnjs1, efac)));
                    Expr indRelation = mknary<FORALL>(args1);

                    u.serialize_formula(indRelation);
                  }
                }
              }
            }
          }
        }
      }

      /*
      // find all combinations of inductive rules based on equations from the formulas
      vector<int> combs;
      for (auto & v : argsInd1)
      {
        assert (tmp[v].size() > 0);
        combs.push_back(tmp[v].size());
      }

      vector<vector<int>> res;
      getCombinations(combs, res);
      for (auto & a : res)
      {
        ExprVector args;
        ExprVector argsVars;
        int i = 0;
        for (auto & v : argsInd1)
        {
          args.push_back(tmp[v][a[i]]);
          filter (args.back(), bind::IsConst (), inserter(argsVars, argsVars.begin()));
          i++;
        }
        Expr app = bind::fapp (rel, args);
        ExprSet filteredConstraints;
        for (auto & o : otherConstraints)
        {
          Expr c = replaceAll(o, argsInd1, args);
          if (!hasExtraVars(c, argsVars)) filteredConstraints.insert(c);
        }
        filteredConstraints.insert(indApp2);
        Expr indDef = mk<EQ>(app, conjoin(filteredConstraints, efac));

        // serialize inductive case

        ExprSet vars;
        ExprVector args1;

        filter(indDef, bind::IsConst (), inserter(vars, vars.begin()));
        for (auto & a : vars)
        {
          if (a != baseCon)
          {
            args1.push_back(a->last());
//            tmp.push_back(a);
          }
        }
        args1.push_back(indDef);
        Expr indRelation = mknary<FORALL>(args1);
        u.serialize_formula(indRelation);

        // TODO: integrate with ADTSolver.hpp and generate lemmas
      }
       */
    }

    static void getCombinations(vector<int>& combs, vector<vector<int>>& res)
    {
      for (int i = 0; i < combs[0]; i++)
      {
        vector<int> tmp;
        tmp.push_back(i);
        res.push_back(tmp);
      }
      for (int pos = 1; pos < combs.size(); pos++)
      {
        int sz = res.size();
        for (int i = 0; i < sz; i++)
        {
          res[i].push_back(0);
          for (int j = 1; j < combs[pos]; j++)
          {
            vector<int> tmp = res[i];
            tmp.back() = j;
            res.push_back(tmp);
          }
        }
      }
    }
  };

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

  static inline void simSynt(ExprFactory& efac, EZ3& z3, Expr s1, Expr s2)
  {
    ExprVector constructors;
    for (auto & a : z3.getAdtConstructors()) constructors.push_back(a);
    ExprVector ops1;
    ExprVector ops2;
    getConj(s1, ops1);
    getConj(s2, ops2);
    SimSynt sim(efac, ops1, ops2);
    sim.proc(constructors);
  }
}

#endif
