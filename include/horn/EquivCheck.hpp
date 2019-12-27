#ifndef EQUIVHECK__HPP__
#define EQUIVHECK__HPP__

#include "Horn.hpp"
#include "CandChecker.hpp"
#include "ae/SMTUtils.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  inline void checkPrerequisites (CHCs& r)
  {
    if (r.decls.size() > 1)
    {
      outs() << "Nested loops not supported\n";
      exit(0);
    }

    if (r.chcs.size() < 2)
    {
      outs() << "Please provide a file with at least two rules (INIT and TR)\n";
      exit(0);
    }

    HornRuleExt* tr = NULL;
    HornRuleExt* fc = NULL;

    for (auto & a : r.chcs)
      if (a.isInductive) tr = &a;
      else if (a.isFact) fc = &a;

    if (tr == NULL)
    {
      outs() << "TR is missing\n";
      exit(0);
    }

    if (fc == NULL)
    {
      outs() << "INIT is missing\n";
      exit(0);
    }
  }

  inline void equivCheck(string chcfile1, string chcfile2, int mode)
  {
    ExprFactory efac;
    EZ3 z3(efac);

    // Mode 0: default, check if the transition body of 2 programs are equivalent
    // Mode > 0: emulate BMC, start from init, append transition n = Mode times, check equivalence
    outs() << "Current mode: " << mode << "\n";

    CHCs ruleManager1(efac, z3);
    ruleManager1.parse(chcfile1, "v_");
    checkPrerequisites(ruleManager1);
    outs () << "Program encoding #1:\n";
    ruleManager1.print();



    CHCs ruleManager2(efac, z3);
    ruleManager2.parse(chcfile2, "w_");
    checkPrerequisites(ruleManager2);
    outs () << "Program encoding #2:\n";
    ruleManager2.print();

    // TODO: check equivalence between programs encoded in ruleManager1 and ruleManager2

    SMTUtils utils(efac);

    if (mode == 0) {

      Expr body1, body2;

      ExprVector srcVars1, srcVars2, dstVars1, dstVars2;

      for (auto &hr: ruleManager1.chcs){
        if (hr.isInductive) {
          body1 = hr.body;
          srcVars1 = hr.srcVars;
          dstVars1 = hr.dstVars;
        }
      }

      for (auto &hr: ruleManager2.chcs){
        if (hr.isInductive) {
          body2 = hr.body;
          srcVars2 = hr.srcVars;
          dstVars2 = hr.dstVars;
        }
      }

      Expr product = mk<AND>(body1, body2);
      Expr out_eq = mk<TRUE>(efac);

      if (srcVars1.size() != srcVars2.size() || dstVars1.size() != dstVars2.size()) {
        outs() << "NOT equiv!\n";
      } else {
        for (int i = 0; i < srcVars1.size(); i++) {
          product = mk<AND>(product, mk<EQ>(srcVars1[i], srcVars2[i]));
        }
        for (int i = 0; i < dstVars1.size(); i++) {
          //product = mk<AND>(product, mk<NEG>(mk<EQ>(dstVars1[i], dstVars2[i])));
          out_eq = mk<AND>(out_eq, mk<EQ>(dstVars1[i], dstVars2[i]));
        }
        Expr product_neg = mk<AND>(product, mk<NEG>(out_eq));
        Expr product_pos = mk<AND>(product, out_eq);
        outs() << "Product:\n" << * product_neg << "\n";
        if ((!utils.isSat(product_neg)) && utils.isSat(product_pos)) outs() << "EQUIV!\n";
        else outs() << "NOT equiv!\n";
      }
    }

    else if (mode > 0) {
      outs() << "INTO BMC emulation\n";

      Expr init_body1, init_body2, transit_body1, transit_body2;

      ExprVector init_srcVars1, init_srcVars2, init_dstVars1, init_dstVars2;
      ExprVector transit_srcVars1, transit_srcVars2, transit_dstVars1, transit_dstVars2;
      ExprVector locVars1, locVars2;



      for (auto &hr: ruleManager1.chcs){
        if (hr.isInductive) {
          transit_body1 = hr.body;
          transit_srcVars1 = hr.srcVars;
          transit_dstVars1 = hr.dstVars;
          locVars1 = hr.locVars;
          outs() << "transit 1 var size\n" << transit_srcVars1.size() << ", " << transit_dstVars1.size() << ", " << hr.locVars.size() << "\n";
        }
        if (hr.isFact) {
          init_body1 = hr.body;
          init_dstVars1 = hr.dstVars;
          outs() << "init 1 var size\n" << init_dstVars1.size() << ", " << hr.locVars.size() << "\n";
        }
      }

      if (isOpX<AND>(transit_body1)) {
        outs() << "transition is AND\n" << transit_body1->arity() << "\n" << *transit_body1 << "\n";
        outs() << * transit_body1->arg(0) << "\n";
        if (isOpX<AND>(transit_body1->arg(0))) {
          outs() << "inside also AND\n" << transit_body1->arg(0)->arity() << "\n";
        }

        if (isOpX<EQ>(transit_body1->arg(1))) {
          outs() << "second inside is EQ\n";
        }
        //for (auto it = transit_body1->args_begin(), end = transit_body1->args_end(); it != end; ++it){
        //  outs() << *it << "\n";
        //}
        exit(0);
      }

      for (auto &hr: ruleManager2.chcs){
        if (hr.isInductive) {
          transit_body2 = hr.body;
          transit_srcVars2 = hr.srcVars;
          transit_dstVars2 = hr.dstVars;
          locVars2 = hr.locVars;
          outs() << "transit 2 var size\n" << transit_srcVars2.size() << ", " << transit_dstVars2.size() << ", " << hr.locVars.size() << "\n";
        }
        if (hr.isFact) {
          init_body2 = hr.body;
          init_dstVars2 = hr.dstVars;
          outs() << "init 2 var size\n" << init_dstVars2.size() << ", " << hr.locVars.size() << "\n";
        }
      }

      if (transit_srcVars1.size() != transit_srcVars2.size() || transit_dstVars1.size() != transit_dstVars2.size() || transit_srcVars1.size() != transit_dstVars1.size()) {
        outs() << "NOT equiv!\n";
        exit(0);
      }

      if (init_dstVars1.size() != transit_srcVars1.size() || init_dstVars2.size() != transit_srcVars2.size()) {
        outs() << "INIT and BODY should be applied to same vars\n";
        exit(0);
      } else {
        Expr new_init1, new_init2;
        new_init1 = init_body1;
        new_init2 = init_body2;

        for (int i = 0; i < init_dstVars1.size(); i++) {
          new_init1 = replaceAll(new_init1, init_dstVars1[i], transit_srcVars1[i]);
        }

        for (int i = 0; i < init_dstVars2.size(); i++) {
          new_init2 = replaceAll(new_init2, init_dstVars2[i], transit_srcVars2[i]);
        }

        if (!utils.isSat(new_init1)) {
          outs() << "prog 1 init can't be satisfied, invalid program!\nNOT equiv!\n";
          exit(0);
        }

        if (!utils.isSat(new_init2)) {
          outs() << "prog 2 init can't be satisfied, invalid program!\nNOT equiv!\n";
          exit(0);
        }

        //outs() << "init 1\n" << * new_init1 << "\n";
        //outs() << "init 2\n" << * new_init2 << "\n";

        Expr prog1 = mk<AND>(new_init1, transit_body1);
        Expr prog2 = mk<AND>(new_init2, transit_body2);

        if (!utils.isSat(prog1)) {
          outs() << "prog1 invalid after unwinding 1 time, invalid program!\nNOT equiv!\n";
          exit(0);
        }

        if (!utils.isSat(prog2)) {
          outs() << "prog2 invalid after unwinding 1 time, invalid program!\nNOT euiqv!\n";
          exit(0);
        }

        init_srcVars1 = transit_srcVars1;
        init_srcVars2 = transit_srcVars2;


        for (int i = 1; i < mode; i++ ) {
          ExprVector new_iter_dstVars1, new_iter_dstVars2;
          ExprVector new_locVars1, new_locVars2;
          // Mode defines the number of iterations to unwind
          for (int k = 0; k < transit_dstVars1.size(); k++) {
            Expr new_name1 = mkTerm<string> ("prog1_unwind_" + to_string(i) + "_" + to_string(k), efac);
            Expr var1 = cloneVar(transit_dstVars1[k], new_name1);
            new_iter_dstVars1.push_back(var1);

            Expr new_name2 = mkTerm<string> ("prog2_unwind_" + to_string(i) + "_" + to_string(k), efac);
            Expr var2 = cloneVar(transit_dstVars2[k], new_name2);
            new_iter_dstVars2.push_back(var2);

            transit_body1 = replaceAll(transit_body1, transit_dstVars1[k], var1);
            transit_body2 = replaceAll(transit_body2, transit_dstVars2[k], var2);
          }

          for (int k = 0; k < locVars1.size(); k++) {
            Expr new_name1 = mkTerm<string> ("prog1_unwind_loc" + to_string(i) + "_" + to_string(k), efac);
            Expr var1 = cloneVar(locVars1[k], new_name1);
            new_locVars1.push_back(var1);
            transit_body1 = replaceAll(transit_body1, locVars1[k], var1);
          }

          for (int k = 0; k < locVars2.size(); k++) {
            Expr new_name2 = mkTerm<string> ("prog2_unwind_loc" + to_string(i) + "_" + to_string(k), efac);
            Expr var2 = cloneVar(locVars2[k], new_name2);
            new_locVars2.push_back(var2);
            transit_body2 = replaceAll(transit_body2, locVars2[k], var2);
          }

          for (int k = 0; k < transit_srcVars1.size(); k++) {
            transit_body1 = replaceAll(transit_body1, transit_srcVars1[k], transit_dstVars1[k]);
            transit_body2 = replaceAll(transit_body2, transit_srcVars2[k], transit_dstVars2[k]);
          }

          //outs () << "new body1\n" << * transit_body1 << "\n";
          //outs () << "new body2\n" << * transit_body2 << "\n";

          prog1 = mk<AND>(prog1, transit_body1);
          prog2 = mk<AND>(prog2, transit_body2);

          transit_srcVars1 = transit_dstVars1;
          transit_srcVars2 = transit_dstVars2;
          transit_dstVars1 = new_iter_dstVars1;
          transit_dstVars2 = new_iter_dstVars2;
          locVars1 = new_locVars1;
          locVars2 = new_locVars2;

          if (!utils.isSat(prog1)) {
            outs() << "prog1 invalid after unwinding " << i + 1 << " times, invalid program!\nNOT equiv!\n";
            exit(0);
          }

          if (!utils.isSat(prog2)) {
            outs() << "prog2 invalid after unwinding " << i + 1 << " times, invalid program!\nNOT euiqv!\n";
            exit(0);
          }
        }

        //outs() << "new var size: " << new_iter_dstVars1.size() << "\n";
        //for(auto &a: new_iter_dstVars1) outs() << *a << ", ";
        //outs() << "\n";

        outs() << "prog 1\n" << * prog1 << "\n";
        outs() << "prog 2\n" << * prog2 << "\n";

        Expr product = mk<AND>(prog1, prog2);
        Expr out_eq = mk<TRUE>(efac);

        for (int i = 0; i < transit_srcVars1.size(); i++) {
          product = mk<AND>(product, mk<EQ>(init_srcVars1[i], init_srcVars2[i]));
        }

        if (!utils.isSat(product)) {
          outs() << "product program invalid!\nNOT equiv!\n";
          exit(0);
        }

        for (int i = 0; i < transit_dstVars1.size(); i++) {
          //product = mk<AND>(product, mk<NEG>(mk<EQ>(dstVars1[i], dstVars2[i])));
          out_eq = mk<AND>(out_eq, mk<EQ>(transit_dstVars1[i], transit_dstVars2[i]));
        }
        //product = mk<AND>(product, mk<NEG>(out_eq));

        Expr product_neg = mk<AND>(product, mk<NEG>(out_eq));
        Expr product_pos = mk<AND>(product, out_eq);
        outs() << "Product:\n" << * product_neg << "\n";
        if ((!utils.isSat(product_neg)) && utils.isSat(product_pos)) outs() << "EQUIV!\n";
        else outs() << "NOT equiv!\n";

        //outs() << "product prog\n" << * product << "\n";

        //if (!utils.isSat(product)) outs() << "EQUIV!\n";
        //else outs() << "NOT equiv!\n";
      }
    }
    else if (mode == -1) {
      // this mode is to verify loop coverage
      // emulate python range(), only experimental
      Expr body1, body2;
      ExprVector srcVars1, srcVars2, dstVars1, dstVars2;

      for (auto &hr: ruleManager1.chcs){
        if (hr.isInductive) {
          body1 = hr.body;
          srcVars1 = hr.srcVars;
          dstVars1 = hr.dstVars;
        }
      }

      for (auto &hr: ruleManager2.chcs){
        if (hr.isInductive) {
          body2 = hr.body;
          srcVars2 = hr.srcVars;
          dstVars2 = hr.dstVars;
        }
      }

      if (srcVars1.size() != srcVars2.size()) {
        outs() << "NOT equiv!\n";
        exit(0);
      }

      for (int i = 0; i < srcVars1.size(); i++) {
        body2 = replaceAll(body2, srcVars2[i], srcVars1[i]);
      }

      if (dstVars1.size() != dstVars2.size()) {
        outs() << "NOT equiv!\n";
        exit(0);
      }

      for (int i = 0; i < dstVars1.size(); i++) {
        body2 = replaceAll(body2, dstVars2[i], dstVars1[i]);
      }

      outs() << "body 1" << * body1 << "\n";
      outs() << "body 2" << * body2 << "\n";

      if (utils.isEquiv(body1, body2)) outs() << "EQUIV!\n";
      else outs() << "NOT equiv!\n";
    }
  };

}

#endif
