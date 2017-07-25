/**
 * List::MoreUtils::XS
 * Copyright 2004 - 2010 by by Tassilo von Parseval
 * Copyright 2013 - 2017 by Jens Rehsack
 *
 * All code added with 0.417 or later is licensed under the Apache License,
 * Version 2.0 (the "License"); you may not use this file except in compliance
 * with the License. You may obtain a copy of the License at
 * 
 *  http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 * 
 * All code until 0.416 is licensed under the same terms as Perl itself,
 * either Perl version 5.8.4 or, at your option, any later version of
 * Perl 5 you may have available.
 */

#define NEED_gv_fetchpvn_flags
#define PERL_NO_GET_CONTEXT

#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"
#include "multicall.h"

#include "ppport.h"

#include "LMUconfig.h"

#ifndef aTHX
#  define aTHX
#  define pTHX
#endif

#ifndef croak_xs_usage

# ifndef PERL_ARGS_ASSERT_CROAK_XS_USAGE
#  define PERL_ARGS_ASSERT_CROAK_XS_USAGE assert(cv); assert(params)
# endif

static void
S_croak_xs_usage(pTHX_ const CV *const cv, const char *const params)
{
    const GV *const gv = CvGV(cv);

    PERL_ARGS_ASSERT_CROAK_XS_USAGE;

    if (gv) {
        const char *const gvname = GvNAME(gv);
        const HV *const stash = GvSTASH(gv);
        const char *const hvname = stash ? HvNAME(stash) : NULL;

        if (hvname)
            Perl_croak_nocontext("Usage: %s::%s(%s)", hvname, gvname, params);
        else
            Perl_croak_nocontext("Usage: %s(%s)", gvname, params);
    } else {
        /* Pants. I don't think that it should be possible to get here. */
        Perl_croak_nocontext("Usage: CODE(0x%"UVxf")(%s)", PTR2UV(cv), params);
    }
}

# define croak_xs_usage(a,b)     S_croak_xs_usage(aTHX_ a,b)
#endif

#ifdef SVf_IVisUV
#  define slu_sv_value(sv) (SvIOK(sv)) ? (SvIOK_UV(sv)) ? (NV)(SvUVX(sv)) : (NV)(SvIVX(sv)) : (SvNV(sv))
#else
#  define slu_sv_value(sv) (SvIOK(sv)) ? (NV)(SvIVX(sv)) : (SvNV(sv))
#endif

/*
 * Perl < 5.18 had some kind of different SvIV_please_nomg
 */
#if PERL_VERSION < 18
#undef SvIV_please_nomg
#  define SvIV_please_nomg(sv) \
        (!SvIOKp(sv) && (SvNOK(sv) || SvPOK(sv)) \
            ? (SvIV_nomg(sv), SvIOK(sv))          \
            : SvIOK(sv))
#endif

#ifndef MUTABLE_GV
# define MUTABLE_GV(a) (GV *)(a)
#endif
#ifndef LIKELY
# define LIKELY(x) (x)
#endif
#ifndef UNLIKELY
# define UNLIKELY(x) (x)
#endif
#ifndef GV_NOTQUAL
# define GV_NOTQUAL 0
#endif

/* compare left and right SVs. Returns:
 * -1: <
 *  0: ==
 *  1: >
 *  2: left or right was a NaN
 */
static I32
LMUncmp(pTHX_ SV* left, SV * right)
{
    /* Fortunately it seems NaN isn't IOK */
    if(SvAMAGIC(left) || SvAMAGIC(right))
        return SvIVX(amagic_call(left, right, ncmp_amg, 0));

    if (SvIV_please_nomg(right) && SvIV_please_nomg(left))
    {
        if (!SvUOK(left))
        {
            const IV leftiv = SvIVX(left);
            if (!SvUOK(right))
            {
                /* ## IV <=> IV ## */
                const IV rightiv = SvIVX(right);
                return (leftiv > rightiv) - (leftiv < rightiv);
            }
            /* ## IV <=> UV ## */
            if (leftiv < 0)
                /* As (b) is a UV, it's >=0, so it must be < */
                return -1;

            return ((UV)leftiv > SvUVX(right)) - ((UV)leftiv < SvUVX(right));
        }

        if (SvUOK(right))
        {
            /* ## UV <=> UV ## */
            const UV leftuv = SvUVX(left);
            const UV rightuv = SvUVX(right);
            return (leftuv > rightuv) - (leftuv < rightuv);
        }

        /* ## UV <=> IV ## */
        if (SvIVX(right) < 0)
            /* As (a) is a UV, it's >=0, so it cannot be < */
            return 1;

        return (SvUVX(left) > SvUVX(right)) - (SvUVX(left) < SvUVX(right));
    }
    else
    {
#ifdef SvNV_nomg
        NV const rnv = SvNV_nomg(right);
        NV const lnv = SvNV_nomg(left);
#else
        NV const rnv = slu_sv_value(right);
        NV const lnv = slu_sv_value(left);
#endif

#if defined(NAN_COMPARE_BROKEN) && defined(Perl_isnan)
        if (Perl_isnan(lnv) || Perl_isnan(rnv))
            return 2;
        return (lnv > rnv) - (lnv < rnv);
#else
        if (lnv < rnv)
            return -1;
        if (lnv > rnv)
            return 1;
        if (lnv == rnv)
            return 0;
        return 2;
#endif
    }
}

#define ncmp(left,right) LMUncmp(aTHX_ left,right)

#define FUNC_NAME GvNAME(GvEGV(ST(items)))

/* shameless stolen from PadWalker */
#ifndef PadARRAY
typedef AV PADNAMELIST;
typedef SV PADNAME;
# if PERL_VERSION < 8 || (PERL_VERSION == 8 && !PERL_SUBVERSION)
typedef AV PADLIST;
typedef AV PAD;
# endif
# define PadlistARRAY(pl)       ((PAD **)AvARRAY(pl))
# define PadlistMAX(pl)         av_len(pl)
# define PadlistNAMES(pl)       (*PadlistARRAY(pl))
# define PadnamelistARRAY(pnl)  ((PADNAME **)AvARRAY(pnl))
# define PadnamelistMAX(pnl)    av_len(pnl)
# define PadARRAY               AvARRAY
# define PadnameIsOUR(pn)       !!(SvFLAGS(pn) & SVpad_OUR)
# define PadnameOURSTASH(pn)    SvOURSTASH(pn)
# define PadnameOUTER(pn)       !!SvFAKE(pn)
# define PadnamePV(pn)          (SvPOKp(pn) ? SvPVX(pn) : NULL)
#endif
#ifndef PadnameSV
# define PadnameSV(pn)          pn
#endif
#ifndef PadnameFLAGS
# define PadnameFLAGS(pn)       (SvFLAGS(PadnameSV(pn)))
#endif

static int 
in_pad (pTHX_ SV *code)
{
    GV *gv;
    HV *stash;
    CV *cv = sv_2cv(code, &stash, &gv, 0);
    PADLIST *pad_list = (CvPADLIST(cv));
    PADNAMELIST *pad_namelist = PadlistNAMES(pad_list);
    int i;

    for (i=PadnamelistMAX(pad_namelist); i>=0; --i)
    {
        PADNAME* name_sv = PadnamelistARRAY(pad_namelist)[i];
        if (name_sv)
        {
            char *name_str = PadnamePV(name_sv);
            if (name_str) {

                /* perl < 5.6.0 does not yet have our */
#               ifdef SVpad_OUR
                if(PadnameIsOUR(name_sv))
                    continue;
#               endif

                if (!(PadnameFLAGS(name_sv)) & SVf_OK)
                    continue;

                if (strEQ(name_str, "$a") || strEQ(name_str, "$b"))
                    return 1;
            }
        }
    }
    return 0;
}

#define WARN_OFF \
    SV *oldwarn = PL_curcop->cop_warnings; \
    PL_curcop->cop_warnings = pWARN_NONE;

#define WARN_ON \
    PL_curcop->cop_warnings = oldwarn;

#define EACH_ARRAY_BODY \
        int i;                                                                          \
        arrayeach_args * args;                                                          \
        HV *stash = gv_stashpv("List::MoreUtils::XS_ea", TRUE);                         \
        CV *closure = newXS(NULL, XS_List__MoreUtils__XS__array_iterator, __FILE__);    \
                                                                                        \
        /* prototype */                                                                 \
        sv_setpv((SV*)closure, ";$");                                                   \
                                                                                        \
        New(0, args, 1, arrayeach_args);                                                \
        New(0, args->avs, items, AV*);                                                  \
        args->navs = items;                                                             \
        args->curidx = 0;                                                               \
                                                                                        \
        for (i = 0; i < items; i++) {                                                   \
            if(!arraylike(ST(i)))                                                       \
               croak_xs_usage(cv,  "\\@;\\@\\@...");                                    \
            args->avs[i] = (AV*)SvRV(ST(i));                                            \
            SvREFCNT_inc(args->avs[i]);                                                 \
        }                                                                               \
                                                                                        \
        CvXSUBANY(closure).any_ptr = args;                                              \
        RETVAL = newRV_noinc((SV*)closure);                                             \
                                                                                        \
        /* in order to allow proper cleanup in DESTROY-handler */                       \
        sv_bless(RETVAL, stash)

#define LMUFECPY(a) (a)
#define dMULTICALLSVCV                          \
        HV *stash;                              \
        GV *gv;                                 \
        I32 gimme = G_SCALAR;                   \
        CV *mc_cv = sv_2cv(code, &stash, &gv, 0)


#define FOR_EACH(on_item)                       \
    if(!codelike(code))                         \
       croak_xs_usage(cv,  "code, ...");        \
                                                \
    if (items > 1) {                            \
        dMULTICALL;                             \
        dMULTICALLSVCV;                         \
        int i;                                  \
        SV **args = &PL_stack_base[ax];         \
        PUSH_MULTICALL(mc_cv);                  \
        SAVESPTR(GvSV(PL_defgv));               \
                                                \
        for(i = 1 ; i < items ; ++i) {          \
            GvSV(PL_defgv) = LMUFECPY(args[i]); \
            MULTICALL;                          \
            on_item;                            \
        }                                       \
        POP_MULTICALL;                          \
    }

#define TRUE_JUNCTION                             \
    FOR_EACH(if (SvTRUE(*PL_stack_sp)) ON_TRUE)   \
    else ON_EMPTY;

#define FALSE_JUNCTION                            \
    FOR_EACH(if (!SvTRUE(*PL_stack_sp)) ON_FALSE) \
    else ON_EMPTY;

#define ROF_EACH(on_item)                       \
    if(!codelike(code))                         \
       croak_xs_usage(cv,  "code, ...");        \
                                                \
    if (items > 1) {                            \
        dMULTICALL;                             \
        dMULTICALLSVCV;                         \
        int i;                                  \
        SV **args = &PL_stack_base[ax];         \
        PUSH_MULTICALL(mc_cv);                  \
        SAVESPTR(GvSV(PL_defgv));               \
                                                \
        for(i = items-1; i > 0; --i) {          \
            GvSV(PL_defgv) = LMUFECPY(args[i]); \
            MULTICALL;                          \
            on_item;                            \
        }                                       \
        POP_MULTICALL;                          \
    }

#define COUNT_ARGS                                    \
    for (i = 0; i < items; i++) {                     \
        SvGETMAGIC(args[i]);                          \
        if(SvOK(args[i])) {                           \
            HE *he;                                   \
            SvSetSV_nosteal(tmp, args[i]);            \
            he = hv_fetch_ent(hv, tmp, 0, 0);         \
            if (NULL == he) {                         \
                args[count++] = args[i];              \
                hv_store_ent(hv, tmp, newSViv(1), 0); \
            }                                         \
            else {                                    \
                SV *v = HeVAL(he);                    \
                IV how_many = SvIVX(v);               \
                sv_setiv(v, ++how_many);              \
            }                                         \
        }                                             \
        else if(0 == seen_undef++) {                  \
            args[count++] = args[i];                  \
        }                                             \
    }


/* #include "dhash.h" */

/* need this one for array_each() */
typedef struct
{
    AV **avs;       /* arrays over which to iterate in parallel */
    int navs;       /* number of arrays */
    int curidx;     /* the current index of the iterator */
} arrayeach_args;

/* used for natatime */
typedef struct
{
    SV **svs;
    int nsvs;
    int curidx;
    int natatime;
} natatime_args;

static void
insert_after (pTHX_ int idx, SV *what, AV *av)
{
    int i, len;
    av_extend(av, (len = av_len(av) + 1));

    for (i = len; i > idx+1; i--)
    {
        SV **sv = av_fetch(av, i-1, FALSE);
        SvREFCNT_inc(*sv);
        av_store(av, i, *sv);
    }

    if (!av_store(av, idx+1, what))
        SvREFCNT_dec(what);
}

static int
is_like(pTHX_ SV *sv, const char *like)
{
    int likely = 0;
    if( sv_isobject( sv ) )
    {
        dSP;
        int count;

        ENTER;
        SAVETMPS;
        PUSHMARK(SP);
        XPUSHs( sv_2mortal( newSVsv( sv ) ) );
        XPUSHs( sv_2mortal( newSVpv( like, strlen(like) ) ) );
        PUTBACK;

        if( ( count = call_pv("overload::Method", G_SCALAR) ) )
        {
            I32 ax;
            SPAGAIN;

            SP -= count;
            ax = (SP - PL_stack_base) + 1;
            if( SvTRUE(ST(0)) )
                ++likely;
        }

        FREETMPS;
        LEAVE;
    }

    return likely;
}

static int
is_array(SV *sv)
{
    return SvROK(sv) && ( SVt_PVAV == SvTYPE(SvRV(sv) ) );
}

static int
LMUcodelike(pTHX_ SV *code)
{
    SvGETMAGIC(code);
    return SvROK(code) && ( ( SVt_PVCV == SvTYPE(SvRV(code)) ) || ( is_like(aTHX_ code, "&{}" ) ) );
}

#define codelike(code) LMUcodelike(aTHX_ code)

static int
LMUarraylike(pTHX_ SV *array)
{
    SvGETMAGIC(array);
    return is_array(array) || is_like(aTHX_ array, "@{}" );
}

#define arraylike(array) LMUarraylike(aTHX_ array)

static void
LMUav2flat(pTHX_ AV *tgt, AV *args)
{
    I32 k = 0, j = av_len(args) + 1;

    av_extend(tgt, AvFILLp(tgt) + j);

    while( --j >= 0 )
    {
        SV *sv = *av_fetch(args, k++, FALSE);
        if(arraylike(sv))
        {
            AV *av = (AV *)SvRV(sv);
            LMUav2flat(aTHX_ tgt, av);
        }
        else
        {
            // av_push(tgt, newSVsv(sv));
            av_push(tgt, SvREFCNT_inc(sv));
        }
    }
}

/*-
 * Copyright (c) 1992, 1993
 *      The Regents of the University of California.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#ifndef MIN
# define        MIN(a,b) (((a)<(b))?(a):(b))
#endif

/*
 * FreeBSD's Qsort routine from Bentley & McIlroy's "Engineering a Sort Function".
 * Modified for using Perl Sub (no XSUB) via MULTICALL and all values are SV **
 */
static inline void
swapfunc(SV **a, SV **b, size_t n)
{
    SV **pa = a;
    SV **pb = b;
    while(n-- > 0)
    {
        SV *t = *pa;
        *pa++ = *pb;
        *pb++ = t;
    }
}

#define swap(a, b)    \
    do {              \
        SV *t = *(a); \
        *(a) = *(b);  \
        *(b) = t;     \
    } while(0)

#define vecswap(a, b, n)  \
    if ((n) > 0) swapfunc(a, b, n)

#define CMP(x, y) ({ \
        GvSV(PL_firstgv) = *(x); \
        GvSV(PL_secondgv) = *(y); \
        MULTICALL; \
        SvIV(*PL_stack_sp); \
    })

#define MED3(a, b, c) ( \
    CMP(a, b) < 0 ? \
       (CMP(b, c) < 0 ? b : (CMP(a, c) < 0 ? c : a )) \
      :(CMP(b, c) > 0 ? b : (CMP(a, c) < 0 ? a : c )) \
)

static void
bsd_qsort_r(pTHX_ SV **ary, size_t nelem, OP *multicall_cop)
{
    SV **pa, **pb, **pc, **pd, **pl, **pm, **pn;
    size_t d1, d2;
    int cmp_result, swap_cnt = 0;

loop:
    if (nelem < 7)
    {
        for (pm = ary + 1; pm < ary + nelem; ++pm)
            for (pl = pm; 
                 pl > ary && CMP(pl - 1, pl) > 0;
                 pl -= 1)
                swap(pl, pl - 1);

        return;
    }

    pm = ary + (nelem / 2);
    if (nelem > 7)
    {
        pl = ary;
        pn = ary + (nelem - 1);
        if (nelem > 40)
        {
            size_t d = (nelem / 8);

            pl = MED3(pl, pl + d, pl + 2 * d);
            pm = MED3(pm - d, pm, pm + d);
            pn = MED3(pn - 2 * d, pn - d, pn);
        }
        pm = MED3(pl, pm, pn);
    }
    swap(ary, pm);
    pa = pb = ary + 1;

    pc = pd = ary + (nelem - 1);
    for (;;)
    {
        while (pb <= pc && (cmp_result = CMP(pb, ary)) <= 0)
        {
            if (cmp_result == 0)
            {
                swap_cnt = 1;
                swap(pa, pb);
                pa += 1;
            }

            pb += 1;
        }

        while (pb <= pc && (cmp_result = CMP(pc, ary)) >= 0)
        {
            if (cmp_result == 0)
            {
                swap_cnt = 1;
                swap(pc, pd);
                pd -= 1;
            }
            pc -= 1;
        }

        if (pb > pc)
            break;

        swap(pb, pc);
        swap_cnt = 1;
        pb += 1;
        pc -= 1;
    }
    if (swap_cnt == 0)
    {  /* Switch to insertion sort */
        for (pm = ary + 1; pm < ary + nelem; pm += 1)
            for (pl = pm; 
                 pl > ary && CMP(pl - 1, pl) > 0;
                 pl -= 1)
                swap(pl, pl - 1);
        return;
    }

    pn = ary + nelem;
    d1 = MIN(pa - ary, pb - pa);
    vecswap(ary, pb - d1, d1);
    d1 = MIN(pd - pc, pn - pd - 1);
    vecswap(pb, pn - d1, d1);

    d1 = pb - pa;
    d2 = pd - pc;
    if (d1 <= d2)
    {
        /* Recurse on left partition, then iterate on right partition */
        if (d1 > 1)
            bsd_qsort_r(aTHX_ ary, d1, multicall_cop);

        if (d2 > 1)
        {
            /* Iterate rather than recurse to save stack space */
            /* qsort(pn - d2, d2, multicall_cop); */
            ary = pn - d2;
            nelem = d2;
            goto loop;
        }
    }
    else
    {
        /* Recurse on right partition, then iterate on left partition */
        if (d2 > 1)
            bsd_qsort_r(aTHX_ pn - d2, d2, multicall_cop);

        if (d1 > 1)
        {
            /* Iterate rather than recurse to save stack space */
            /* qsort(ary, d1, multicall_cop); */
            nelem = d1;
            goto loop;
        }
    }
}

#ifdef HAVE_TIME_H
# include <time.h>
#endif
#ifdef HAVE_SYS_TIME_H
# include <sys/time.h>
#endif

MODULE = List::MoreUtils::XS_ea             PACKAGE = List::MoreUtils::XS_ea

void
DESTROY(sv)
SV *sv;
CODE:
{
    int i;
    CV *code = (CV*)SvRV(sv);
    arrayeach_args *args = (arrayeach_args *)(CvXSUBANY(code).any_ptr);
    if (args)
    {
        for (i = 0; i < args->navs; ++i)
            SvREFCNT_dec(args->avs[i]);

        Safefree(args->avs);
        Safefree(args);
        CvXSUBANY(code).any_ptr = NULL;
    }
}


MODULE = List::MoreUtils::XS_na             PACKAGE = List::MoreUtils::XS_na

void
DESTROY(sv)
SV *sv;
CODE:
{
    int i;
    CV *code = (CV*)SvRV(sv);
    natatime_args *args = (natatime_args *)(CvXSUBANY(code).any_ptr);
    if (args)
    {
        for (i = 0; i < args->nsvs; ++i)
            SvREFCNT_dec(args->svs[i]);

        Safefree(args->svs);
        Safefree(args);
        CvXSUBANY(code).any_ptr = NULL;
    }
}

MODULE = List::MoreUtils::XS            PACKAGE = List::MoreUtils::XS

void
any (code,...)
    SV *code;
PROTOTYPE: &@
CODE:
{
#define ON_TRUE { POP_MULTICALL; XSRETURN_YES; }
#define ON_EMPTY XSRETURN_NO
    TRUE_JUNCTION;
    XSRETURN_NO;
#undef ON_EMPTY
#undef ON_TRUE
}

void
all (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
#define ON_FALSE { POP_MULTICALL; XSRETURN_NO; }
#define ON_EMPTY XSRETURN_YES
    FALSE_JUNCTION;
    XSRETURN_YES;
#undef ON_EMPTY
#undef ON_FALSE
}


void
none (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
#define ON_TRUE { POP_MULTICALL; XSRETURN_NO; }
#define ON_EMPTY XSRETURN_YES
    TRUE_JUNCTION;
    XSRETURN_YES;
#undef ON_EMPTY
#undef ON_TRUE
}

void
notall (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
#define ON_FALSE { POP_MULTICALL; XSRETURN_YES; }
#define ON_EMPTY XSRETURN_NO
    FALSE_JUNCTION;
    XSRETURN_NO;
#undef ON_EMPTY
#undef ON_FALSE
}

void
one (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    int found = 0;
#define ON_TRUE { if (found++) { POP_MULTICALL; XSRETURN_NO; }; }
#define ON_EMPTY XSRETURN_YES
    TRUE_JUNCTION;
    if (found)
        XSRETURN_YES;
    XSRETURN_NO;
#undef ON_EMPTY
#undef ON_TRUE
}

void
any_u (code,...)
    SV *code;
PROTOTYPE: &@
CODE:
{
#define ON_TRUE { POP_MULTICALL; XSRETURN_YES; }
#define ON_EMPTY XSRETURN_UNDEF
    TRUE_JUNCTION;
    XSRETURN_NO;
#undef ON_EMPTY
#undef ON_TRUE
}

void
all_u (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
#define ON_FALSE { POP_MULTICALL; XSRETURN_NO; }
#define ON_EMPTY XSRETURN_UNDEF
    FALSE_JUNCTION;
    XSRETURN_YES;
#undef ON_EMPTY
#undef ON_FALSE
}


void
none_u (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
#define ON_TRUE { POP_MULTICALL; XSRETURN_NO; }
#define ON_EMPTY XSRETURN_UNDEF
    TRUE_JUNCTION;
    XSRETURN_YES;
#undef ON_EMPTY
#undef ON_TRUE
}

void
notall_u (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
#define ON_FALSE { POP_MULTICALL; XSRETURN_YES; }
#define ON_EMPTY XSRETURN_UNDEF
    FALSE_JUNCTION;
    XSRETURN_NO;
#undef ON_EMPTY
#undef ON_FALSE
}

void
one_u (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    int found = 0;
#define ON_TRUE { if (found++) { POP_MULTICALL; XSRETURN_NO; }; }
#define ON_EMPTY XSRETURN_UNDEF
    TRUE_JUNCTION;
    if (found)
        XSRETURN_YES;
    XSRETURN_NO;
#undef ON_EMPTY
#undef ON_TRUE
}

int
true (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    I32 count = 0;
    FOR_EACH(if (SvTRUE(*PL_stack_sp)) count++);
    RETVAL = count;
}
OUTPUT:
    RETVAL

int
false (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    I32 count = 0;
    FOR_EACH(if (!SvTRUE(*PL_stack_sp)) count++);
    RETVAL = count;
}
OUTPUT:
    RETVAL

int
firstidx (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    RETVAL = -1;
    FOR_EACH(if (SvTRUE(*PL_stack_sp)) { RETVAL = i-1; break; });
}
OUTPUT:
    RETVAL

SV *
firstval (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    RETVAL = &PL_sv_undef;
    FOR_EACH(if (SvTRUE(*PL_stack_sp)) { SvREFCNT_inc(RETVAL = args[i]); break; });
}
OUTPUT:
    RETVAL

SV *
firstres (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    RETVAL = &PL_sv_undef;
    FOR_EACH(if (SvTRUE(*PL_stack_sp)) { SvREFCNT_inc(RETVAL = *PL_stack_sp); break; });
}
OUTPUT:
    RETVAL

int
onlyidx (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    int found = 0;
    RETVAL = -1;
    FOR_EACH(if (SvTRUE(*PL_stack_sp)) { if (found++) {RETVAL = -1; break;} RETVAL = i-1; });
}
OUTPUT:
    RETVAL

SV *
onlyval (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    int found = 0;
    RETVAL = &PL_sv_undef;
    FOR_EACH(if (SvTRUE(*PL_stack_sp)) { if (found++) {SvREFCNT_dec(RETVAL); RETVAL = &PL_sv_undef; break;} SvREFCNT_inc(RETVAL = args[i]); });
}
OUTPUT:
    RETVAL

SV *
onlyres (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    int found = 0;
    RETVAL = &PL_sv_undef;
    FOR_EACH(if (SvTRUE(*PL_stack_sp)) { if (found++) {SvREFCNT_dec(RETVAL); RETVAL = &PL_sv_undef; break;}SvREFCNT_inc(RETVAL = *PL_stack_sp); });
}
OUTPUT:
    RETVAL

int
lastidx (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    RETVAL = -1;
    ROF_EACH(if (SvTRUE(*PL_stack_sp)){RETVAL = i-1;break;})
}
OUTPUT:
    RETVAL

SV *
lastval (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    RETVAL = &PL_sv_undef;
    ROF_EACH(if (SvTRUE(*PL_stack_sp)) { /* see comment in indexes() */ SvREFCNT_inc(RETVAL = args[i]); break; });
}
OUTPUT:
    RETVAL

SV *
lastres (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    RETVAL = &PL_sv_undef;
    ROF_EACH(if (SvTRUE(*PL_stack_sp)) { SvREFCNT_inc(RETVAL = *PL_stack_sp); break; });
}
OUTPUT:
    RETVAL

int
insert_after (code, val, avref)
    SV *code;
    SV *val;
    SV *avref;
PROTOTYPE: &$\@
CODE:
{
    dMULTICALL;
    dMULTICALLSVCV;
    int i;
    int len;
    AV *av;

    if(!codelike(code))
       croak_xs_usage(cv,  "code, val, \\@area_of_operation");
    if(!arraylike(avref))
       croak_xs_usage(cv,  "code, val, \\@area_of_operation");

    av = (AV*)SvRV(avref);
    len = av_len(av);
    RETVAL = 0;

    PUSH_MULTICALL(mc_cv);
    SAVESPTR(GvSV(PL_defgv));

    for (i = 0; i <= len ; ++i)
    {
        GvSV(PL_defgv) = *av_fetch(av, i, FALSE);
        MULTICALL;
        if (SvTRUE(*PL_stack_sp))
        {
            RETVAL = 1;
            break;
        }
    }

    POP_MULTICALL;

    if (RETVAL)
    {
        SvREFCNT_inc(val);
        insert_after(aTHX_ i, val, av);
    }
}
OUTPUT:
    RETVAL

int
insert_after_string (string, val, avref)
    SV *string;
    SV *val;
    SV *avref;
PROTOTYPE: $$\@
CODE:
{
    int i, len;
    AV *av;
    RETVAL = 0;

    if(!arraylike(avref))
       croak_xs_usage(cv,  "string, val, \\@area_of_operation");

    av = (AV*)SvRV(avref);
    len = av_len(av);

    for (i = 0; i <= len ; i++)
    {
        SV **sv = av_fetch(av, i, FALSE);
        if(0 == sv_cmp_locale(string, *sv))
        {
            RETVAL = 1;
            break;
        }
    }

    if (RETVAL)
    {
        SvREFCNT_inc(val);
        insert_after(aTHX_ i, val, av);
    }
}
OUTPUT:
    RETVAL

void
apply (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    if(!codelike(code))
       croak_xs_usage(cv,  "code, ...");

    if (items > 1) {
        dMULTICALL;
        dMULTICALLSVCV;
        int i;
        SV **args = &PL_stack_base[ax];
        AV *rc = newAV();

        sv_2mortal(newRV_noinc((SV*)rc));
        av_extend(rc, items-1);

        PUSH_MULTICALL(mc_cv);
        SAVESPTR(GvSV(PL_defgv));

        for(i = 1 ; i < items ; ++i) {
            av_push(rc, newSVsv(args[i]));
            GvSV(PL_defgv) = AvARRAY(rc)[AvFILLp(rc)];
            MULTICALL;
        }
        POP_MULTICALL;

        for(i = items - 1; i > 0; --i)
        {
            ST(i-1) = sv_2mortal(AvARRAY(rc)[i-1]);
            AvARRAY(rc)[i-1] = NULL;
        }

        AvFILLp(rc) = -1;
    }

    XSRETURN(items-1);
}

void
after (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    int k = items, j;
    FOR_EACH(if (SvTRUE(*PL_stack_sp)) {k=i; break;});
    for (j = k + 1; j < items; ++j)
        ST(j-k-1) = ST(j);

    j = items-k-1;
    XSRETURN(j > 0 ? j : 0);
}

void
after_incl (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    int k = items, j;
    FOR_EACH(if (SvTRUE(*PL_stack_sp)) {k=i; break;});
    for (j = k; j < items; j++)
        ST(j-k) = ST(j);

    XSRETURN(items-k);
}

void
before (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    int k = items - 1;
    FOR_EACH(if (SvTRUE(*PL_stack_sp)) {k=i-1; break;}; args[i-1] = args[i];);

    XSRETURN(k);
}

void
before_incl (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    int k = items - 1;
    FOR_EACH(args[i-1] = args[i]; if (SvTRUE(*PL_stack_sp)) {k=i; break;});

    XSRETURN(k);
}

void
indexes (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    if(!codelike(code))
       croak_xs_usage(cv,  "code, ...");

    if (items > 1) {
        dMULTICALL;
        dMULTICALLSVCV;
        int i;
        SV **args = &PL_stack_base[ax];
        AV *rc = newAV();

        sv_2mortal(newRV_noinc((SV*)rc));
        av_extend(rc, items-1);

        PUSH_MULTICALL(mc_cv);
        SAVESPTR(GvSV(PL_defgv));

        for(i = 1 ; i < items ; ++i)
        {
            GvSV(PL_defgv) = args[i];
            MULTICALL;
            if (SvTRUE(*PL_stack_sp))
                av_push(rc, newSViv(i-1));
        }
        POP_MULTICALL;

        for(i = av_len(rc); i >= 0; --i)
        {
            ST(i) = sv_2mortal(AvARRAY(rc)[i]);
            AvARRAY(rc)[i] = NULL;
        }

        i = AvFILLp(rc) + 1;
        AvFILLp(rc) = -1;

        XSRETURN(i);
    }

    XSRETURN_EMPTY;
}

void
_array_iterator (method = "")
    const char *method;
PROTOTYPE: ;$
CODE:
{
    int i;
    int exhausted = 1;

    /* 'cv' is the hidden argument with which XS_List__MoreUtils__array_iterator (this XSUB)
     * is called. The closure_arg struct is stored in this CV. */

    arrayeach_args *args = (arrayeach_args *)(CvXSUBANY(cv).any_ptr);

    if (strEQ(method, "index"))
    {
        EXTEND(SP, 1);
        ST(0) = args->curidx > 0 ? sv_2mortal(newSViv(args->curidx-1)) : &PL_sv_undef;
        XSRETURN(1);
    }

    EXTEND(SP, args->navs);

    for (i = 0; i < args->navs; i++)
    {
        AV *av = args->avs[i];
        if (args->curidx <= av_len(av))
        {
            ST(i) = sv_2mortal(newSVsv(*av_fetch(av, args->curidx, FALSE)));
            exhausted = 0;
            continue;
        }
        ST(i) = &PL_sv_undef;
    }

    if (exhausted)
        XSRETURN_EMPTY;

    args->curidx++;
    XSRETURN(args->navs);
}

SV *
each_array (...)
PROTOTYPE: \@;\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@
CODE:
{
    EACH_ARRAY_BODY;
}
OUTPUT:
    RETVAL

SV *
each_arrayref (...)
CODE:
{
    EACH_ARRAY_BODY;
}
OUTPUT:
    RETVAL

void
pairwise (code, list1, list2)
    SV *code;
    AV *list1;
    AV *list2;
PROTOTYPE: &\@\@
PPCODE:
{
    dMULTICALL;
    dMULTICALLSVCV;
    int i, maxitems;
    AV *rc = newAV();
    sv_2mortal(newRV_noinc((SV*)rc));

    if(!codelike(code))
       croak_xs_usage(cv,  "code, list, list");

    if (in_pad(aTHX_ code)) {
        croak("Can't use lexical $a or $b in pairwise code block");
    }

    /* deref AV's for convenience and
     * get maximum items */
    maxitems = MAX(av_len(list1),av_len(list2))+1;
    av_extend(rc, maxitems);

    gimme = G_ARRAY;
    PUSH_MULTICALL(mc_cv);

    if (!PL_firstgv || !PL_secondgv)
    {
        SAVESPTR(PL_firstgv);
        SAVESPTR(PL_secondgv);
        PL_firstgv = gv_fetchpv("a", TRUE, SVt_PV);
        PL_secondgv = gv_fetchpv("b", TRUE, SVt_PV);
    }

    for (i = 0; i < maxitems; ++i)
    {
        SV **j;
        SV **svp = av_fetch(list1, i, FALSE);
        GvSV(PL_firstgv) = svp ? *svp : &PL_sv_undef;
        svp = av_fetch(list2, i, FALSE);
        GvSV(PL_secondgv) = svp ? *svp : &PL_sv_undef;
        MULTICALL;

        for (j = PL_stack_base+1; j <= PL_stack_sp; ++j)
            av_push(rc, newSVsv(*j));
    }

    POP_MULTICALL;

    SPAGAIN;
    EXTEND(SP, AvFILLp(rc) + 1);

    for(i = AvFILLp(rc); i >= 0; --i)
    {
        ST(i) = sv_2mortal(AvARRAY(rc)[i]);
        AvARRAY(rc)[i] = NULL;
    }

    i = AvFILLp(rc) + 1;
    AvFILLp(rc) = -1;

    XSRETURN(i);
}

void
_natatime_iterator ()
PROTOTYPE:
CODE:
{
    int i, nret;

    /* 'cv' is the hidden argument with which XS_List__MoreUtils__array_iterator (this XSUB)
     * is called. The closure_arg struct is stored in this CV. */

    natatime_args *args = (natatime_args*)CvXSUBANY(cv).any_ptr;
    nret = args->natatime;

    EXTEND(SP, nret);

    for (i = 0; i < args->natatime; i++)
        if (args->curidx < args->nsvs)
            ST(i) = sv_2mortal(newSVsv(args->svs[args->curidx++]));
        else
            XSRETURN(i);

    XSRETURN(nret);
}

SV *
natatime (n, ...)
int n;
PROTOTYPE: $@
CODE:
{
    int i;
    natatime_args *args;
    HV *stash = gv_stashpv("List::MoreUtils::XS_na", TRUE);

    CV *closure = newXS(NULL, XS_List__MoreUtils__XS__natatime_iterator, __FILE__);

    /* must NOT set prototype on iterator:
     * otherwise one cannot write: &$it */
    /* !! sv_setpv((SV*)closure, ""); !! */

    New(0, args, 1, natatime_args);
    New(0, args->svs, items-1, SV*);
    args->nsvs = items-1;
    args->curidx = 0;
    args->natatime = n;

    for (i = 1; i < items; i++)
        SvREFCNT_inc(args->svs[i-1] = ST(i));

    CvXSUBANY(closure).any_ptr = args;
    RETVAL = newRV_noinc((SV*)closure);

    /* in order to allow proper cleanup in DESTROY-handler */
    sv_bless(RETVAL, stash);
}
OUTPUT:
    RETVAL

void
arrayify(...)
CODE:
{
    I32 i;
    AV *rc = newAV();
    AV *args = av_make(items, &PL_stack_base[ax]);
    sv_2mortal(newRV_noinc((SV *)rc));
    sv_2mortal(newRV_noinc((SV *)args));

    LMUav2flat(aTHX_ rc, args);

    for(i = AvFILLp(rc); i >= 0; --i)
    {
        ST(i) = sv_2mortal(AvARRAY(rc)[i]);
        AvARRAY(rc)[i] = NULL;
    }

    i = AvFILLp(rc) + 1;
    AvFILLp(rc) = -1;

    XSRETURN(i);
}

void
mesh (...)
PROTOTYPE: \@\@;\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@
CODE:
{
    int i, j, maxidx = -1;
    AV **avs;
    New(0, avs, items, AV*);

    for (i = 0; i < items; i++)
    {
        if(!arraylike(ST(i)))
           croak_xs_usage(cv,  "\\@\\@;\\@...");

        avs[i] = (AV*)SvRV(ST(i));
        if (av_len(avs[i]) > maxidx)
            maxidx = av_len(avs[i]);
    }

    EXTEND(SP, items * (maxidx + 1));
    for (i = 0; i <= maxidx; i++)
        for (j = 0; j < items; j++)
        {
            SV **svp = av_fetch(avs[j], i, FALSE);
            ST(i*items + j) = svp ? sv_2mortal(newSVsv(*svp)) : &PL_sv_undef;
        }

    Safefree(avs);
    XSRETURN(items * (maxidx + 1));
}

HV *
listcmp (...)
PROTOTYPE: \@\@;\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@\@
CODE:
{
    I32 i;
    SV *tmp = sv_newmortal();
    RETVAL = newHV();
    sv_2mortal (newRV_noinc((SV *)RETVAL));

    for (i = 0; i < items; i++)
    {
        AV *av;
        I32 j;
        HV *distinct = newHV();
        sv_2mortal(newRV_noinc((SV*)distinct));

        if(!arraylike(ST(i)))
           croak_xs_usage(cv,  "\\@\\@;\\@...");
        av = (AV*)SvRV(ST(i));

        for(j = 0; j <= av_len(av); ++j)
        {
            SV **sv = av_fetch(av, j, FALSE);
            AV *store;

            if(NULL == sv)
                continue;

            SvGETMAGIC(*sv);
            if(SvOK(*sv))
            {
                SvSetSV_nosteal(tmp, *sv);
                if(hv_exists_ent(distinct, tmp, 0))
                    continue;

                hv_store_ent(distinct, tmp, &PL_sv_yes, 0);

                if(hv_exists_ent(RETVAL, *sv, 0))
                {
                    HE *he = hv_fetch_ent(RETVAL, *sv, 1, 0);
                    store = (AV*)SvRV(HeVAL(he));
                    av_push(store, newSViv(i));
                }
                else
                {
                    store = newAV();
                    av_push(store, newSViv(i));
                    hv_store_ent(RETVAL, tmp, newRV_noinc((SV *)store), 0);
                }
            }
        }
    }
}
OUTPUT:
    RETVAL

void
uniq (...)
PROTOTYPE: @
CODE:
{
    I32 i;
    IV count = 0, seen_undef = 0;
    HV *hv = newHV();
    SV **args = &PL_stack_base[ax];
    SV *tmp = sv_newmortal();
    sv_2mortal(newRV_noinc((SV*)hv));

    /* don't build return list in scalar context */
    if (GIMME_V == G_SCALAR)
    {
        for (i = 0; i < items; i++)
        {
            SvGETMAGIC(args[i]);
            if(SvOK(args[i]))
            {
                sv_setsv_nomg(tmp, args[i]);
                if (!hv_exists_ent(hv, tmp, 0))
                {
                    ++count;
                    hv_store_ent(hv, tmp, &PL_sv_yes, 0);
                }
            }
            else if(0 == seen_undef++)
                ++count;
        }
        ST(0) = sv_2mortal(newSVuv(count));
        XSRETURN(1);
    }

    /* list context: populate SP with mortal copies */
    for (i = 0; i < items; i++)
    {
        SvGETMAGIC(args[i]);
        if(SvOK(args[i]))
        {
            SvSetSV_nosteal(tmp, args[i]);
            if (!hv_exists_ent(hv, tmp, 0))
            {
                /*ST(count) = sv_2mortal(newSVsv(ST(i)));
                ++count;*/
                args[count++] = args[i];
                hv_store_ent(hv, tmp, &PL_sv_yes, 0);
            }
        }
        else if(0 == seen_undef++)
            args[count++] = args[i];
    }

    XSRETURN(count);
}

void
singleton (...)
PROTOTYPE: @
CODE:
{
    I32 i;
    IV cnt = 0, count = 0, seen_undef = 0;
    HV *hv = newHV();
    SV **args = &PL_stack_base[ax];
    SV *tmp = sv_newmortal();

    sv_2mortal(newRV_noinc((SV*)hv));

    COUNT_ARGS

    /* don't build return list in scalar context */
    if (GIMME_V == G_SCALAR)
    {
        for (i = 0; i < count; i++)
        {
            if(SvOK(args[i]))
            {
                HE *he;
                sv_setsv_nomg(tmp, args[i]);
                he = hv_fetch_ent(hv, tmp, 0, 0);
                if (he)
                    if( 1 == SvIVX(HeVAL(he)) )
                        ++cnt;
            }
            else if(1 == seen_undef)
                ++cnt;
        }
        ST(0) = sv_2mortal(newSViv(cnt));
        XSRETURN(1);
    }

    /* list context: populate SP with mortal copies */
    for (i = 0; i < count; i++)
    {
        if(SvOK(args[i]))
        {
            HE *he;
            SvSetSV_nosteal(tmp, args[i]);
            he = hv_fetch_ent(hv, tmp, 0, 0);
            if (he)
                if( 1 == SvIVX(HeVAL(he)) )
                    args[cnt++] = args[i];
        }
        else if(1 == seen_undef)
            args[cnt++] = args[i];
    }

    XSRETURN(cnt);
}

void
duplicates (...)
PROTOTYPE: @
CODE:
{
    I32 i;
    IV cnt = 0, count = 0, seen_undef = 0;
    HV *hv = newHV();
    SV **args = &PL_stack_base[ax];
    SV *tmp = sv_newmortal();

    sv_2mortal(newRV_noinc((SV*)hv));

    COUNT_ARGS

    /* don't build return list in scalar context */
    if (GIMME_V == G_SCALAR)
    {
        for (i = 0; i < count; i++)
        {
            if(SvOK(args[i]))
            {
                HE *he;
                sv_setsv_nomg(tmp, args[i]);
                he = hv_fetch_ent(hv, tmp, 0, 0);
                if (he)
                    if( 1 < SvIVX(HeVAL(he)) )
                        ++cnt;
            }
            else if(1 < seen_undef)
                ++cnt;
        }
        ST(0) = sv_2mortal(newSViv(cnt));
        XSRETURN(1);
    }

    /* list context: populate SP with mortal copies */
    for (i = 0; i < count; i++)
    {
        if(SvOK(args[i]))
        {
            HE *he;
            SvSetSV_nosteal(tmp, args[i]);
            he = hv_fetch_ent(hv, tmp, 0, 0);
            if (he)
                if( 1 < SvIVX(HeVAL(he)) )
                    args[cnt++] = args[i];
        }
        else if(1 < seen_undef) {
            args[cnt++] = args[i];
        }
    }

    XSRETURN(cnt);
}

void
samples (k, ...)
  I32 k;
PROTOTYPE: $@
CODE:
{
    I32 i;

    if( k > (items - 1) )
        croak("Cannot get %d samples from %d elements", k, items-1);

    /* Initialize Drand01 unless rand() or srand() has already been called */
    if(!PL_srand_called)
    {
#ifdef HAVE_TIME
        /* using time(NULL) as seed seems to get better random numbers ... */
        (void)seedDrand01((Rand_seed_t)time(NULL));
#else
        (void)seedDrand01((Rand_seed_t)Perl_seed(aTHX));
#endif
        PL_srand_called = TRUE;
    }

    /* optimzed Knuth-Shuffle since we move our stack one item downwards
       with each exchange */
    for (i = items ; items - i < k ; )
    {
        I32 index = items - i + 1;
        I32 swap = index + (I32)(Drand01() * (double)(--i));
        ST(index-1) = ST(swap);
        ST(swap) = ST(index);
    }

    XSRETURN(k);
}

void
minmax (...)
PROTOTYPE: @
CODE:
{
    I32 i;
    SV *minsv, *maxsv;

    if (!items)
        XSRETURN_EMPTY;

    if (items == 1)
    {
        EXTEND(SP, 1);
        ST(1) = sv_2mortal(newSVsv(ST(0)));
        XSRETURN(2);
    }

    minsv = maxsv = ST(0);

    for (i = 1; i < items; i += 2)
    {
        SV *asv = ST(i-1);
        SV *bsv = ST(i);
        int cmp = ncmp(asv, bsv);
        if (cmp < 0)
        {
            int min_cmp = ncmp(minsv, asv);
            int max_cmp = ncmp(maxsv, bsv);
            if (min_cmp > 0)
                minsv = asv;
            if (max_cmp < 0)
                maxsv = bsv;
        }
        else
        {
            int min_cmp = ncmp(minsv, bsv);
            int max_cmp = ncmp(maxsv, asv);
            if (min_cmp > 0)
                minsv = bsv;
            if (max_cmp < 0)
                maxsv = asv;
        }
    }

    if (items & 1)
    {
        SV *rsv = ST(items-1);
        if (ncmp(minsv, rsv) > 0)
            minsv = rsv;
        else if (ncmp(maxsv, rsv) < 0)
            maxsv = rsv;
    }

    ST(0) = minsv;
    ST(1) = maxsv;

    XSRETURN(2);
}

void
minmaxstr (...)
PROTOTYPE: @
CODE:
{
    I32 i;
    SV *minsv, *maxsv;

    if (!items)
        XSRETURN_EMPTY;

    if (items == 1)
    {
        EXTEND(SP, 1);
        ST(1) = sv_2mortal(newSVsv(ST(0)));
        XSRETURN(2);
    }

    minsv = maxsv = ST(0);

    for (i = 1; i < items; i += 2)
    {
        SV *asv = ST(i-1);
        SV *bsv = ST(i);
        int cmp = sv_cmp_locale(asv, bsv);
        if (cmp < 0)
        {
            int min_cmp = sv_cmp_locale(minsv, asv);
            int max_cmp = sv_cmp_locale(maxsv, bsv);
            if (min_cmp > 0)
                minsv = asv;
            if (max_cmp < 0)
                maxsv = bsv;
        }
        else
        {
            int min_cmp = sv_cmp_locale(minsv, bsv);
            int max_cmp = sv_cmp_locale(maxsv, asv);
            if (min_cmp > 0)
                minsv = bsv;
            if (max_cmp < 0)
                maxsv = asv;
        }
    }

    if (items & 1)
    {
        SV *rsv = ST(items-1);
        if (sv_cmp_locale(minsv, rsv) > 0)
            minsv = rsv;
        else if (sv_cmp_locale(maxsv, rsv) < 0)
            maxsv = rsv;
    }

    ST(0) = minsv;
    ST(1) = maxsv;

    XSRETURN(2);
}

void
part (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    dMULTICALL;
    dMULTICALLSVCV;
    int i;
    SV **args = &PL_stack_base[ax];
    AV *tmp = newAV();
    sv_2mortal(newRV_noinc((SV*)tmp));

    if(!codelike(code))
       croak_xs_usage(cv,  "code, ...");

    if (items == 1)
        XSRETURN_EMPTY;

    PUSH_MULTICALL(mc_cv);
    SAVESPTR(GvSV(PL_defgv));

    for(i = 1 ; i < items ; ++i)
    {
        IV idx;
        SV **inner;
        AV *av;

        GvSV(PL_defgv) = args[i];
        MULTICALL;
        idx = SvIV(*PL_stack_sp);

        if (UNLIKELY(idx < 0 && (idx += (AvFILLp(tmp)+1)) < 0))
            croak("Modification of non-creatable array value attempted, subscript %ld", idx);

        if(UNLIKELY(NULL == (inner = av_fetch(tmp, idx, FALSE))))
        {
            av = newAV();
            av_push(av, newSVsv(args[i]));
            av_store(tmp, idx, newRV_noinc((SV *)av));
        }
        else
        {
            av = (AV*)SvRV(*inner);
            av_push(av, newSVsv(args[i]));
        }
    }
    POP_MULTICALL;

    EXTEND(SP, AvFILLp(tmp)+1);
    for(i = AvFILLp(tmp); i >= 0; --i)
    {
        SV *v = AvARRAY(tmp)[i];
        ST(i) = v && is_array(v) ? sv_2mortal(v) : &PL_sv_undef;
        AvARRAY(tmp)[i] = NULL;
    }

    i = AvFILLp(tmp) + 1;
    AvFILLp(tmp) = -1;

    XSRETURN(i);
}

#if 0
void
part_dhash (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    /* We might want to keep this dhash-implementation.
     * It is currently slower than the above but it uses less
     * memory for sparse parts such as
     *   @part = part { 10_000_000 } 1 .. 100_000;
     * Maybe there's a way to optimize dhash.h to get more speed
     * from it.
     */
    dMULTICALL;
    int i, j, lastidx = -1;
    int max;
    HV *stash;
    GV *gv;
    I32 gimme = G_SCALAR;
    I32 count = 0;
    SV **args = &PL_stack_base[ax];
    CV *cv;

    dhash_t *h = dhash_init();

    if(!codelike(code))
       croak_xs_usage(cv,  "code, ...");

    if (items == 1)
        XSRETURN_EMPTY;

    cv = sv_2cv(code, &stash, &gv, 0);
    PUSH_MULTICALL(cv);
    SAVESPTR(GvSV(PL_defgv));

    for(i = 1 ; i < items ; ++i) {
        int idx;
        GvSV(PL_defgv) = args[i];
        MULTICALL;
        idx = SvIV(*PL_stack_sp);

        if (idx < 0 && (idx += h->max) < 0)
            croak("Modification of non-creatable array value attempted, subscript %i", idx);

        dhash_store(h, idx, args[i]);
    }
    POP_MULTICALL;

    dhash_sort_final(h);

    EXTEND(SP, max = h->max+1);
    i = 0;
    lastidx = -1;
    while (i < h->count) {
        int retidx = h->ary[i].key;
        int fill = retidx - lastidx - 1;
        for (j = 0; j < fill; j++) {
            ST(retidx - j - 1) = &PL_sv_undef;
        }
        ST(retidx) = newRV_noinc((SV*)h->ary[i].val);
        i++;
        lastidx = retidx;
    }

    dhash_destroy(h);
    XSRETURN(max);
}

#endif

SV *
bsearch (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    dMULTICALL;
    HV *stash;
    GV *gv;
    I32 gimme = GIMME_V; /* perl-5.5.4 bus-errors out later when using GIMME
                            therefore we save its value in a fresh variable */
    SV **args = &PL_stack_base[ax];

    long i, j;
    int val = -1;

    if(!codelike(code))
       croak_xs_usage(cv,  "code, ...");

    if (items > 1)
    {
        CV *_cv = sv_2cv(code, &stash, &gv, 0);
        PUSH_MULTICALL(_cv);
        SAVESPTR(GvSV(PL_defgv));

        i = 0;
        j = items - 1;
        do
        {
            long k = (i + j) / 2;

            if (k >= items-1)
                break;

            GvSV(PL_defgv) = args[1+k];
            MULTICALL;
            val = SvIV(*PL_stack_sp);

            if (val == 0)
            {
                POP_MULTICALL;
                if (gimme != G_ARRAY)
                    XSRETURN_YES;
                SvREFCNT_inc(RETVAL = args[1+k]);
                goto yes;
            }
            if (val < 0)
                i = k+1;
            else
                j = k-1;
        } while (i <= j);
        POP_MULTICALL;
    }

    if (gimme == G_ARRAY)
        XSRETURN_EMPTY;
    else
        XSRETURN_UNDEF;
yes:
    ;
}
OUTPUT:
    RETVAL

int
bsearchidx (code, ...)
    SV *code;
PROTOTYPE: &@
CODE:
{
    dMULTICALL;
    HV *stash;
    GV *gv;
    I32 gimme = GIMME_V; /* perl-5.5.4 bus-errors out later when using GIMME
                            therefore we save its value in a fresh variable */
    SV **args = &PL_stack_base[ax];

    long i, j;
    int val = -1;

    if(!codelike(code))
       croak_xs_usage(cv,  "code, ...");

    RETVAL = -1;

    if (items > 1)
    {
        CV *_cv = sv_2cv(code, &stash, &gv, 0);
        PUSH_MULTICALL(_cv);
        SAVESPTR(GvSV(PL_defgv));

        i = 0;
        j = items - 1;
        do
        {
            long k = (i + j) / 2;

            if (k >= items-1)
                break;

            GvSV(PL_defgv) = args[1+k];
            MULTICALL;
            val = SvIV(*PL_stack_sp);

            if (val == 0)
            {
                RETVAL = k;
                break;
            }
            if (val < 0)
                i = k+1;
            else
                j = k-1;
        } while (i <= j);
        POP_MULTICALL;
    }
}
OUTPUT:
    RETVAL

int
binsert(code, item, list)
    SV *code;
    SV *item;
    AV *list;
PROTOTYPE: &$\@
CODE:
{
    I32 gimme = GIMME_V; /* perl-5.5.4 bus-errors out later when using GIMME
                            therefore we save its value in a fresh variable */
    if(!codelike(code))
       croak_xs_usage(cv,  "code, val, list");

    RETVAL = -1;

    if (av_len(list) > 0)
    {
        dMULTICALL;
        HV *stash;
        GV *gv;
        ssize_t count = av_len(list) + 1, step, first = 0;
        int cmprc = -1;
        SV **btree = AvARRAY(list);

        CV *_cv = sv_2cv(code, &stash, &gv, 0);
        PUSH_MULTICALL(_cv);
        SAVESPTR(GvSV(PL_defgv));

        /* lower_bound algorithm from STL */
        while (count > 0)
        {
            ssize_t it = first;
            step = count / 2; 
            it += step;

            GvSV(PL_defgv) = btree[it];
            MULTICALL;
            cmprc = SvIV(*PL_stack_sp);
            if (cmprc < 0)
            {
                first = ++it; 
                count -= step + 1; 
            }
            else
                count = step;
        }

        POP_MULTICALL;

        SvREFCNT_inc(item);
        insert_after(aTHX_ (RETVAL = first) - 1, item, list);
    }
}
OUTPUT:
    RETVAL

void
bremove(code, list)
    SV *code;
    AV *list;
PROTOTYPE: &\@
CODE:
{
    dMULTICALL;
    HV *stash;
    GV *gv;
    I32 gimme = GIMME_V; /* perl-5.5.4 bus-errors out later when using GIMME
                            therefore we save its value in a fresh variable */
    long i, j;
    int val = -1;

    if(!codelike(code))
       croak_xs_usage(cv,  "code, ...");

    if (av_len(list) > 0)
    {
        CV *_cv = sv_2cv(code, &stash, &gv, 0);
        PUSH_MULTICALL(_cv);
        SAVESPTR(GvSV(PL_defgv));

        i = 0;
        j = av_len(list);
        do
        {
            long k = (i + j) / 2;

            if (k > av_len(list))
                break;

            GvSV(PL_defgv) = *av_fetch(list, k, FALSE);
            MULTICALL;
            val = SvIV(*PL_stack_sp);

            if (val == 0)
            {
                POP_MULTICALL;

                if(av_len(list) == k)
                {
                    ST(0) = sv_2mortal(av_pop(list));
                    XSRETURN(1);
                }

                if(0 == k )
                {
                    ST(0) = sv_2mortal(av_shift(list));
                    XSRETURN(1);
                }

                ST(0) = av_delete(list, k, 0);
                for(i = k; i < av_len(list); ++i)
                {
                    SV **sv = av_fetch(list, i+1, FALSE);
                    if(sv)
                    {
                        SvREFCNT_inc(*sv);
                        av_store(list, i, *sv);
                    }
                }
                av_delete(list, av_len(list), G_DISCARD);
#if PERL_VERSION_LE(5,8,5)
                sv_2mortal(ST(0));
#endif
                XSRETURN(1);
            }
            if (val < 0)
                i = k+1;
            else
                j = k-1;
        } while (i <= j);
        POP_MULTICALL;
    }

    if (gimme == G_ARRAY)
        XSRETURN_EMPTY;
    else
        XSRETURN_UNDEF;
}

void
qsort(code, list)
    SV *code;
    AV *list;
PROTOTYPE: &\@
CODE:
{
    I32 gimme = GIMME_V; /* perl-5.5.4 bus-errors out later when using GIMME
                            therefore we save its value in a fresh variable */
    dMULTICALL;

    if(!codelike(code))
       croak_xs_usage(cv,  "code, ...");

    if (in_pad(aTHX_ code))
        croak("Can't use lexical $a or $b in qsort's cmp code block");
    
    if (av_len(list) > 0)
    {
        HV *stash;
        GV *gv;
        CV *_cv = sv_2cv(code, &stash, &gv, 0);

        PUSH_MULTICALL(_cv);

        SAVEGENERICSV(PL_firstgv);
        SAVEGENERICSV(PL_secondgv);
        PL_firstgv = MUTABLE_GV(SvREFCNT_inc(
            gv_fetchpvs("a", GV_ADD|GV_NOTQUAL, SVt_PV)
        ));
        PL_secondgv = MUTABLE_GV(SvREFCNT_inc(
            gv_fetchpvs("b", GV_ADD|GV_NOTQUAL, SVt_PV)
        ));
        /* make sure the GP isn't removed out from under us for
         * the SAVESPTR() */
        save_gp(PL_firstgv, 0);
        save_gp(PL_secondgv, 0);
        /* we don't want modifications localized */
        GvINTRO_off(PL_firstgv);
        GvINTRO_off(PL_secondgv);
        SAVESPTR(GvSV(PL_firstgv));
        SAVESPTR(GvSV(PL_secondgv));

        bsd_qsort_r(aTHX_ AvARRAY(list), av_len(list) + 1, multicall_cop);
        POP_MULTICALL;
    }
}

void
_XScompiled ()
    CODE:
       XSRETURN_YES;
