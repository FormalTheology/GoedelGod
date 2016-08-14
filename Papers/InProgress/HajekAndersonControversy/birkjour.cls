%%
%% This is file `birkjour.cls',
%% generated using amsart.cls
%% Birkhauser Publishing Ltd., Basel
%%
%%% ====================================================================

\NeedsTeXFormat{LaTeX2e}% LaTeX 2.09 can't be used (nor non-LaTeX)
[1994/12/01]% LaTeX date must December 1994 or later
\ProvidesClass{birkjour}[2009/09/04 v6.0]
% 6.0 T1 format included
\def\@tempa#1#2\@nil{\edef\@classname{#1}}
\expandafter\@tempa\@currnamestack{}{}{}\@nil
\ifx\@classname\@empty \edef\@classname{\@currname}\fi
\DeclareOption{a4paper}{\PackageWarning{birkmult}{Option '\CurrentOption' will be ignored}}
\DeclareOption{letterpaper}{\PackageWarning{birkmult}{Option '\CurrentOption' will be ignored}}
\DeclareOption{landscape}{\@tempdima\paperheight
  \paperheight\paperwidth \paperwidth\@tempdima}
\DeclareOption{portrait}{}
\DeclareOption{oneside}{\@twosidefalse \@mparswitchfalse}
\DeclareOption{twoside}{\@twosidetrue  \@mparswitchtrue}
\DeclareOption{draft}{\overfullrule5\p@ }
\DeclareOption{final}{\overfullrule\z@ }
\def\dateposted#1{\def\@dateposted{\ (#1)}}%
\let\@dateposted\@empty
\DeclareOption{e-only}{\PackageWarning{birkmult}{Option '\CurrentOption' will be ignored}}
\newif\if@titlepage
\DeclareOption{titlepage}{\@titlepagetrue}
\DeclareOption{notitlepage}{\@titlepagefalse}
\newif\if@openright
\DeclareOption{openright}{\@openrighttrue}
\DeclareOption{openany}{\@openrightfalse}
\DeclareOption{onecolumn}{\@twocolumnfalse}
\DeclareOption{twocolumn}{\@twocolumntrue}
\DeclareOption{nomath}{\PackageWarning{birkmult}{Option '\CurrentOption' will be ignored}}
\def\mathfrak{needed}
%---------------------
%\@twosidetrue  \@mparswitchfalse
\def\se@ies{}
\newif\ifseries@
\series@false
\newif\ifsecondjournalline@
\secondjournalline@true
\newif\ifDOI@
\DOI@false
\newif\ifMJM@
\MJM@false
\newif\ifADM@
\ADM@false
\newcommand\DOInr[1]{\def\@DOInr{#1}}
\DOInr{}
\newcommand\jourtitle[1]{\def\@jourtitle{#1}}
\jourtitle{}
\newcommand\jourtext[1]{\def\@jourtext{#1}}
\jourtext{}
\newcommand\jourtitlesecond[1]{\def\@jourtitlesecond{#1}}
\jourtitlesecond{}
\newif\ifjournal@
\journal@false
\newcommand\volume[1]{\def\@volume{#1}}
\volume{1}
\newcommand\ISSN[1]{\def\@issn{#1}}
\ISSN{}
\newcommand\seriesextra[1]{\def\@seriesextra{#1}}
\seriesextra{\relax}
\newif\ifseriesextra@
\seriesextra@false
\newcommand\seriesextraline[1]{\def\@seriesextraline{#1}}
\seriesextraline{\relax}
\newif\ifseriesextraline@
\seriesextraline@false
\newif\ifvolume@
\volume@false
\ifvolume@{\volume{1}}\else{\volume{}}\fi
\newif\ifnoendauthors@
\noendauthors@false
\newif\ifteinsformat@
\teinsformat@true
\DeclareOption{acm}{\def\se@ies{Advanced Courses in Mathematics CRM Barcelona}\series@true\CheckClo\teinsformat@false}
\DeclareOption{amfm}{\def\se@ies{Advances in Mathematical Fluid Mechanics}\series@true\CheckClo\teinsformat@false}
\DeclareOption{dmv}{\def\se@ies{Oberwolfach Seminars}\series@true\volume@true\CheckClo\teinsformat@false}
\DeclareOption{isnm}{\def\se@ies{International Series of Numerical Mathematics}\series@true\volume@true\CheckClo\teinsformat@false}
\DeclareOption{mbc}{\def\se@ies{Mathematics and Biosciences in Interaction}\series@true\CheckClo\teinsformat@false}
\DeclareOption{ot}{\def\se@ies{Operator Theory:\br Advances and Applications}\series@true\volume@true\CheckClo\teinsformat@false}
\DeclareOption{pcs}{\def\se@ies{Progress in Computer Science and Applied Logic}\series@true\volume@true\CheckClo\teinsformat@false}
\DeclareOption{pm}{\def\se@ies{Progress in Mathematics}\series@true\volume@true\CheckClo\teinsformat@false}
\DeclareOption{pnlde}{\def\se@ies{Progress in Nonlinear Differential Equations\br and Their Applications}\series@true\volume@true\CheckClo\teinsformat@false}
\DeclareOption{pp}{\def\se@ies{Progress in Probability}\series@true\volume@true\CheckClo\teinsformat@false}
\DeclareOption{sit}{\def\se@ies{Statistics for Industry and Technology}\series@true\CheckClo\teinsformat@false}
\DeclareOption{tm}{\def\se@ies{Trends in Mathematics}\series@true\CheckClo\teinsformat@false}
\DeclareOption{wssat}{\def\se@ies{Whitestein Series in Software Agent Technologies}\series@true\CheckClo\teinsformat@false}
\DeclareOption{DOI}{\DOI@true}
\DeclareOption{seriesextra}{\seriesextra@true}
\DeclareOption{seriesextraline}{\seriesextraline@true}
\DeclareOption{noendauthors}{\noendauthors@true}
%---------------------
\DeclareOption{adm}{\ADM@true\def\se@ies{Arch. Math.}\series@true\journal@true\DOInr{s00013}\ISSN{1422-6928}%
\DOI@true\jourtitle{Archiv der Mathematik}\secondjournalline@false\jourtext{\upshape Arch. Math.}\ExecuteOptions{leqno}\CheckClo}
\DeclareOption{jmfm}{\def\se@ies{J. math. fluid. mech.}\series@true\journal@true\DOInr{s00009}\ISSN{1422-6928}%
\DOI@true\jourtitle{Journal of Mathematical}\jourtitlesecond{Fluid Mechanics}\jourtext{JMFM}\CheckClo}
\DeclareOption{ieot}{\def\se@ies{Integr. equ. oper. theory}\series@true\journal@true\DOInr{s00020}\ISSN{0378-620X}%
\DOI@true\jourtitle{Integral Equations}\jourtitlesecond{and Operator Theory}\jourtext{IEOT}\CheckClo}
\DeclareOption{mjm}{\def\se@ies{Milan j. math.}\series@true\journal@true\DOInr{s00032}\ISSN{}%
\DOI@true\jourtitle{Milan Journal of Mathematics}\secondjournalline@false\jourtext{}\def\@mainsize{11}\def\@ptsize{1}%
  \def\@typesizes{%
    \or{6}{7}\or{7}{8}\or{8}{10}\or{9}{11}\or{10}{12}%
    \or{\@xipt}{13}% normalsize
    \or{\@xiipt}{14}\or{\@xivpt}{17}\or{\@xviipt}{20}%
    \or{\@xxpt}{24}\or{\@xxvpt}{30}}%
  \normalsize \linespacing=\baselineskip\renewcommand\baselinestretch{1.05}\DOInr{s00032}\ISSN{1424-9286}\journal@true
  \MJM@true\CheckClo\teinsformat@false}
\DeclareOption{ahp}{\def\se@ies{Ann. Henri Poincar\'e}\series@true\journal@true\DOInr{s00023}\ISSN{1424-0637}%
\DOI@true\jourtitle{Annales Henri Poincar\'e}\secondjournalline@false\jourtext{Ann. Henri Poincar\'e}\CheckClo}
\DeclareOption{jg}{\def\se@ies{J. geom.}\series@true\journal@true\DOInr{s00022}\ISSN{0047-2468}%
\DOI@true\jourtitle{Journal of Geometry}\secondjournalline@false\jourtext{J. Geom.}\CheckClo}
\DeclareOption{zamp}{\def\se@ies{Z. angew. Math. Phys.}\series@true\journal@true\DOInr{s00033}\ISSN{0044-2275}%
\DOI@true\jourtitle{Zeitschrift f\"ur angewandte}\jourtitlesecond{Mathematik und Physik ZAMP}\jourtext{ZAMP}\CheckClo}
\DeclareOption{medjm}{\def\se@ies{Mediterr. j. math.}\series@true\journal@true\DOInr{s00009}\ISSN{1660-5446}%
\DOI@true\jourtitle{Mediterranean Journal}\jourtitlesecond{of Mathematics}\jourtext{Mediterr. j. math.}\CheckClo\teinsformat@false}
\DeclareOption{sm}{\def\se@ies{Sel. math., New ser.}\series@true\journal@true\DOInr{s00029}\ISSN{1022-1824}%
\DOI@true\jourtitle{Selecta Mathematica}\jourtitlesecond{New Series}\jourtext{Sel. math., New ser.}\CheckClo}
\DeclareOption{aaca}{\def\se@ies{Adv. appl. Clifford alg.}\series@true\journal@true\DOInr{s00006}\ISSN{0188-7009}%
\DOI@true\jourtitle{Advances in}\jourtitlesecond{Applied Clifford Algebras}\jourtext{AACA}\CheckClo}
\DeclareOption{pos}{\def\se@ies{Positivity}\series@true\journal@true\DOInr{s11117}\ISSN{1385-1292}%
\DOI@true\jourtitle{Positivity}\secondjournalline@false\jourtext{Positivity}\CheckClo}
\DeclareOption{rm}{\def\se@ies{Result.Math.}\series@true\journal@true\DOInr{s00025}\ISSN{1422-6383}%
\DOI@true\jourtitle{Results in Mathematics}\secondjournalline@false\jourtext{Result.Math.}\CheckClo}
\DeclareOption{caot}{\def\se@ies{Compl. anal. oper. theory}\series@true\journal@true\DOInr{s11785}\ISSN{1661-8254}%
\DOI@true\jourtitle{Complex Analysis}\jourtitlesecond{and Operator Theory}\jourtext{Comp.an.op.th.}\CheckClo}
\DeclareOption{jfpt}{\def\se@ies{J. fixed point theory appl.}\series@true\journal@true\DOInr{s11784}\ISSN{1661-7738}%
\DOI@true\jourtitle{Journal of Fixed Point Theory}\jourtitlesecond{and Applications}\jourtext{JFPTA}\CheckClo}
\DeclareOption{lu}{\def\se@ies{Logica universalis}\series@true\journal@true\DOInr{s11787}\ISSN{1661-8297}%
\DOI@true\jourtitle{Logica Universalis}\secondjournalline@false\jourtext{Logica universalis}\CheckClo}
\DeclareOption{mic}{\def\se@ies{Math. in comp. sc.}\series@true\journal@true\DOInr{s11786}\ISSN{1661-8270}%
\DOI@true\jourtitle{Mathematics in Computer Science}\secondjournalline@false\jourtext{Math. in Comp. Sc.}\CheckClo}
\DeclareOption{nodea}{\def\se@ies{NoDEA -- Nolinear differ. equ. appl.}\series@true\journal@true\DOInr{s00030}\ISSN{1021-9722}%
\DOI@true\jourtitle{Nonlinear Differential Equations}\jourtitlesecond{and Applications NoDEA}\jourtext{NoDEA}\CheckClo}
\DeclareOption{qtds}{\def\se@ies{Qual. Th. Dyn. Syst.}\series@true\journal@true\DOInr{s12346}\ISSN{1575-5460}%
\DOI@true\jourtitle{Qualitative Theory}\jourtitlesecond{of Dynamical Systems}\jourtext{Qual. Th. Dyn. Syst.}\CheckClo}
%
% check if a .clo file exists
\newcommand{\CheckClo}{\InputIfFileExists{\CurrentOption.clo}{}{\PackageWarning{birkmult}{Option \CurrentOption.clo\space not recognized}}}

%---------------------
%\DeclareOption*{\PackageWarning{birkmult}{Unknown option '\CurrentOption'}}
\DeclareOption*{\input{\CurrentOption.clo}}
%---------------------
\newcommand\onlinedate[1]{\def\@onlinedate{#1}}
\onlinedate{\relax}
\newif\ifonlinefirst@
\onlinefirst@false
\DeclareOption{onlinefirst}{\onlinefirst@true}
\newif\ifprintsecond@
\printsecond@false
\DeclareOption{printsecond}{\printsecond@true}
%---------------------
\DeclareOption{noamsfonts}{\let\mathfrak\relax}
\DeclareOption{psamsfonts}{%
  \PassOptionsToPackage{psamsfonts}{amsfonts}%
  \PassOptionsToPackage{cmex10}{amsmath}}
\newif\iftagsleft@
\DeclareOption{leqno}{%
  \tagsleft@true \PassOptionsToPackage{leqno}{amsmath}}
\DeclareOption{reqno}{%
  \tagsleft@false \PassOptionsToPackage{reqno}{amsmath}}
\newif\ifctagsplit@
\DeclareOption{centertags}{%
  \ctagsplit@true \PassOptionsToPackage{centertags}{amsmath}}
\DeclareOption{tbtags}{%
  \ctagsplit@false \PassOptionsToPackage{tbtags}{amsmath}}
\DeclareOption{fleqn}{%
  \def\[{\relax
    \ifmmode\@badmath
    \else
      \begin{trivlist}%
      \@beginparpenalty\predisplaypenalty
      \@endparpenalty\postdisplaypenalty
      \item[]\leavevmode
      \hbox to\linewidth\bgroup$\displaystyle
      \hskip\mathindent\bgroup
    \fi}%
  \def\]{\relax
    \ifmmode
      \egroup \m@th$\hfil \egroup
      \end{trivlist}%
    \else \@badmath
    \fi}%
  \renewenvironment{equation}{%
    \@beginparpenalty\predisplaypenalty
    \@endparpenalty\postdisplaypenalty
    \refstepcounter{equation}%
    \@topsep\abovedisplayskip \trivlist
    \item[]\leavevmode
    \hbox to\linewidth\bgroup\hskip\mathindent$\displaystyle
  }{%
    \m@th$\hfil \displaywidth\linewidth \hbox{\@eqnnum}\egroup
    \endtrivlist
  }%
  \renewenvironment{eqnarray}{%
%---changed: \upshape..
    \stepcounter{equation}\let\@currentlabel{{\rm\theequation}}
    \global\@eqnswtrue \global\@eqcnt\z@ \tabskip\mathindent
    \let\\=\@eqncr \abovedisplayskip\topsep
    \ifvmode \advance\abovedisplayskip\partopsep \fi
    \belowdisplayskip\abovedisplayskip
    \belowdisplayshortskip\abovedisplayskip
    \abovedisplayshortskip\abovedisplayskip
    $$\everycr{}\halign to\linewidth\bgroup
      \hskip\@centering
      $\displaystyle\tabskip\z@skip####\m@th$&%
      \@eqnsel \global\@eqcnt\@ne
      \hfil${}####{}\m@th$\hfil&%
      \global\@eqcnt\tw@
      $\displaystyle ####\m@th$\hfil\tabskip\@centering&%
      \global\@eqcnt\thr@@
      \hbox to \z@\bgroup\hss####\egroup\tabskip\z@skip\cr
    }{%
      \@@eqncr \egroup \global\advance\c@equation\m@ne$$%
      \global\@ignoretrue
    }%
  \newdimen\mathindent \mathindent\leftmargini
}
\newcommand{\@mainsize}{10}
\newcommand{\@ptsize}{0}
\newcommand{\larger}[1][1]{%
  \count@\@currsizeindex \advance\count@#1\relax
 \ifnum\count@<\z@ \count@\z@ \else\ifnum\count@>12 \count@12 \fi\fi
  \ifcase\count@
    \Tiny\or\Tiny\or\tiny\or\SMALL\or\Small\or\small
    \or\normalsize
    \or\large\or\Large\or\LARGE\or\huge\or\Huge\else\Huge
  \fi
}
\newcommand{\smaller}[1][1]{\larger[-#1]}
\def\@adjustvertspacing{%
  \bigskipamount.7\baselineskip plus.7\baselineskip
  \medskipamount\bigskipamount \divide\medskipamount\tw@
  \smallskipamount\medskipamount \divide\smallskipamount\tw@
  \abovedisplayskip\medskipamount
  \belowdisplayskip \abovedisplayskip
  \abovedisplayshortskip\abovedisplayskip
 \advance\abovedisplayshortskip-1\abovedisplayskip
  \belowdisplayshortskip\abovedisplayshortskip
  \advance\belowdisplayshortskip 1\smallskipamount
  \jot\baselineskip \divide\jot 4 \relax
}
\renewcommand\normalsize{\@xsetfontsize\normalsize 6%
  \@adjustvertspacing \let\@listi\@listI}
\newcommand\Tiny{\@xsetfontsize\Tiny 1}
\newcommand\tiny{\@xsetfontsize\tiny 2}
\newcommand\SMALL{\@xsetfontsize\SMALL 3}
\newcommand\Small{\@xsetfontsize\Small 4%
  \@adjustvertspacing
  \def\@listi{\topsep\smallskipamount \parsep\z@skip \itemsep\z@skip}}
\newcommand\small{\@xsetfontsize\small 5\@adjustvertspacing}
\def\footnotesize{\Small}
\def\scriptsize{\SMALL}
\newcommand\large{\@xsetfontsize\large 7\@adjustvertspacing}
\newcommand\Large{\@xsetfontsize\Large 8\@adjustvertspacing}
\newcommand\LARGE{\@xsetfontsize\LARGE 9}
\newcommand\huge{\@xsetfontsize\huge{10}}
\newcommand\Huge{\@xsetfontsize\Huge{11}}

\def\@xsetfontsize#1#2{%
  \chardef\@currsizeindex#2\relax
  \edef\@tempa{\@nx\@setfontsize\@nx#1%
    \@xp\ifcase\@xp\@currsizeindex\@typesizes
        \else{99}{99}\fi}%
\@tempa
}


\chardef\@currsizeindex=6
\widowpenalty=10000
\clubpenalty=10000
\brokenpenalty=10000
\newdimen\linespacing
\lineskip=1pt \lineskiplimit=1pt
\normallineskip=1pt \normallineskiplimit=1pt
\let\baselinestretch=\@empty
%%\headheight=5pt \headsep=14pt
\headheight=7pt \headsep=18pt
\footskip=12pt
\textheight=50.5pc \topskip=10pt
\textwidth=30pc
\columnsep=10pt \columnseprule=0pt
\marginparwidth=90pt
\marginparsep=11pt
\marginparpush=5pt
\AtBeginDocument{\settoheight{\footnotesep}{\footnotesize M$^1$}}
\skip\footins=7pt plus11pt
\skip\@mpfootins=\skip\footins
\fboxsep=3pt \fboxrule=.4pt
\arrayrulewidth=.4pt    \doublerulesep=2pt
\labelsep=5pt           \arraycolsep=\labelsep
\tabcolsep=\labelsep    \tabbingsep=\labelsep
\floatsep=15pt plus 12pt    \dblfloatsep=15pt plus 12pt
\textfloatsep=\floatsep  \dbltextfloatsep=15pt plus 12pt
\intextsep=\floatsep
\@fptop=0pt plus1fil     \@dblfptop=0pt plus1fil
\@fpbot=0pt plus1fil     \@dblfpbot=0pt plus1fil
\@fpsep=8pt plus2fil     \@dblfpsep=8pt plus2fil\relax
\ifADM@
\parskip=5pt plus1pt minus2pt\relax
\else
\parskip=0pt plus1pt\relax
\fi
\newdimen\normalparindent
\normalparindent=8mm
\parindent=\normalparindent
\partopsep=0pt \relax \parsep=0pt \relax \itemsep=0pt \relax
\@lowpenalty=51         \@medpenalty=151        \@highpenalty=301
\@beginparpenalty=-\@lowpenalty
\@endparpenalty=-\@lowpenalty
\@itempenalty=-\@lowpenalty
\DeclareOption{10pt}{\def\@mainsize{10}\def\@ptsize{0}%
  \def\@typesizes{%
    \or{5}{6}\or{6}{7}\or{7}{8}\or{8}{10}\or{9}{11}%
    \or{10}{12}% normalsize
    \or{\@xipt}{13}\or{\@xiipt}{14}\or{\@xivpt}{17}%
    \or{\@xviipt}{20}\or{\@xxpt}{24}}%
  \normalsize \linespacing=\baselineskip
}
\DeclareOption{11pt}{\PackageWarning{birkmult}{Option '\CurrentOption' will be ignored}}
\DeclareOption{12pt}{\PackageWarning{birkmult}{Option '\CurrentOption' will be ignored}}
\DeclareOption{8pt}{\PackageWarning{birkmult}{Option '\CurrentOption' will be ignored}}
\DeclareOption{9pt}{\PackageWarning{birkmult}{Option '\CurrentOption' will be ignored}}
\def\ps@empty{\let\@mkboth\@gobbletwo
  \let\@oddhead\@empty \let\@evenhead\@empty
  \let\@oddfoot\@empty \let\@evenfoot\@empty
  \global\topskip\normaltopskip}
\def\ps@plain{\ps@empty
  \def\@oddfoot{\normalfont\hfil\thepage\hfil}%
  \let\@evenfoot\@oddfoot}
\def\ps@headings{\ps@empty
  \def\@evenhead{\normalfont\ifjournal@\small\fi
      \rlap{\thepage}\hfil \leftmark{}{}\hfil\ifjournal@\llap{\@jourtext}\fi}%
  \def\@oddhead{\normalfont\ifjournal@\small\fi \ifonlinefirst@\relax\else\ifjournal@\rlap{Vol. \@volyear} \fi\fi\hfil
      \rightmark{}{}\hfil \llap{\thepage}}%
  \let\@mkboth\markboth
}
\let\sectionname\@empty
\let\subsectionname\@empty
\let\subsubsectionname\@empty
\let\paragraphname\@empty
\let\subparagraphname\@empty
\def\leftmark{\expandafter\@firstoftwo\topmark{}{}}
\def\rightmark{\expandafter\@secondoftwo\botmark{}{}}
\def\ps@firstpage{\ps@plain
  \def\@oddfoot{\normalfont \hfil%%\thepage\hfil
     \global\topskip\normaltopskip}%
  \let\@evenfoot\@oddfoot
  \def\@oddhead{\@serieslogo\hss}%
  \let\@evenhead\@oddhead % in case an article starts on a left-hand page
}
\long\def\@nilgobble#1\@nil{}
\def\markboth#1#2{%
  \begingroup
    \@temptokena{{#1}{#2}}\xdef\@themark{\the\@temptokena}%
    \mark{\the\@temptokena}%
  \endgroup
  \if@nobreak\ifvmode\nobreak\fi\fi}
\def\ps@myheadings{\ps@headings \let\@mkboth\@gobbletwo}
\newskip\normaltopskip
\normaltopskip=10pt \relax
\let\sectionmark\@gobble
\let\subsectionmark\@gobble
\let\subsubsectionmark\@gobble
\let\paragraphmark\@gobble

\DeclareOption{makeidx}{}
\input{amsgen.sty}
%\ifADM@\ExecuteOptions{leqno,centertags,portrait,%
%  10pt,twoside,onecolumn,final}
%  \ProcessOptions\relax
%\else
\ExecuteOptions{centertags,portrait,%
  10pt,twoside,onecolumn,final}
  \ProcessOptions\relax
%\fi
%\ProcessOptions\relax
\if@compatibility
  \def\@tempa#1{\let\mathfrak\relax
    \RequirePackage{amstex}\relax}\expandafter\@tempa
\else
  \expandafter\@iden
\fi
{% if native mode
\@ifclasswith{\@classname}{nomath}{%
  \def\numberwithin#1#2{\@ifundefined{c@#1}{\@nocounterr{#1}}{%
    \@ifundefined{c@#2}{\@nocounterr{#2}}{%
    \@addtoreset{#1}{#2}%
    \toks@\@xp\@xp\@xp{\csname the#1\endcsname}%
    \@xp\xdef\csname the#1\endcsname
      {\@xp\@nx\csname the#2\endcsname
       .\the\toks@}}}}%
}{%
  \RequirePackage{amsmath}\relax
}
\@ifclasswith{\@classname}{noamsfonts}{%
}{%
\let\mathfrak\relax
  \IfFileExists{umsa.fd}{%
    \RequirePackage{amsfonts}\relax
  }{IfFileExists{Umsa.fd}{%
      \RequirePackage{amsfonts}\relax
    }{IfFileExists{UMSA.fd}{%
        \RequirePackage{amsfonts}\relax
    }{%
    \ClassError{\@classname
    }{%
      Font description files Umsa.fd et al. not found; amsfonts.sty
      not loaded.
    }{%
      A font description (.fd) file is needed for every font being used;
      these files may be in the inputs area along with other style and
      class files, or in a dedicated subdirectory if your system uses
      a TDS structure.
    }%
  }%
  }%
}%
}%
}% end native mode branch
\RequirePackage{graphicx}
\newcommand{\uppercasenonmath}[1]{\toks@\@emptytoks
  \@xp\@skipmath\@xp\@empty#1$$%
  \edef#1{\@nx\@upprep\the\toks@}%
}
\newcommand{\@upprep}{%
  \spaceskip1.3\fontdimen2\font plus1.3\fontdimen3\font
  \upchars@}
\newcommand{\upchars@}{%
  \def\ss{SS}\def\i{I}\def\j{J}\def\ae{\AE}\def\oe{\OE}%
  \def\o{\O}\def\aa{\AA}\def\l{\L}\def\Mc{M{\scshape c}}}
\newcommand{\@skipmath}{}
\long\def\@skipmath#1$#2${%
  \@xskipmath#1\(\)%
  \@ifnotempty{#2}{\toks@\@xp{\the\toks@$#2$}\@skipmath\@empty}}%
\newcommand{\@xskipmath}{}
\long\def\@xskipmath#1\(#2\){%
  \uppercase{\toks@\@xp\@xp\@xp{\@xp\the\@xp\toks@#1}}%
  \@ifnotempty{#2}{\toks@\@xp{\the\toks@\(#2\)}\@xskipmath\@empty}}%
\newcommand{\today}{%
  \relax\ifcase\month\or
  January\or February\or March\or April\or May\or June\or
  July\or August\or September\or October\or November\or December\fi
  \space\number\day, \number\year}
\DeclareOldFontCommand{\rm}{\normalfont\rmfamily}{\mathrm}
\DeclareOldFontCommand{\sf}{\normalfont\sffamily}{\mathsf}
\DeclareOldFontCommand{\tt}{\normalfont\ttfamily}{\mathtt}
\DeclareOldFontCommand{\bf}{\normalfont\bfseries}{\mathbf}
\DeclareOldFontCommand{\it}{\normalfont\itshape}{\mathit}
\DeclareOldFontCommand{\sl}{\normalfont\slshape}{\@nomath\sl}
\DeclareOldFontCommand{\sc}{\normalfont\scshape}{\@nomath\sc}
\renewcommand*{\title}[2][]{\gdef\shorttitle{#1}\gdef\@title{#2}}
\edef\title{\@nx\@dblarg
  \@xp\@nx\csname\string\title\endcsname}
\renewcommand{\author}[2][]{%
  \ifx\@empty\authors
    \gdef\shortauthors{#1}\gdef\authors{#2}%
    \ifADM@
    \ifnoendauthors@\g@addto@macro\addresses{\noindent}
    \else\g@addto@macro\addresses{{\noindent #2,~}}\fi
    \else
    \ifnoendauthors@\g@addto@macro\addresses{\par\bigskip}%\noindent \br}
    \else\g@addto@macro\addresses{{\par\medskip\noindent #2\br}}\fi
  \fi
  \else
    \g@addto@macro\shortauthors{\and#1}%
    \g@addto@macro\authors{\and#2}
    \ifADM@
    \ifnoendauthors@\g@addto@macro\addresses{\author{}}\g@addto@macro\addresses{\par\medskip}%\noindent \br}
    \else\g@addto@macro\addresses{\noindent #2,~}\fi
    \else
    \ifnoendauthors@\g@addto@macro\addresses{\author{}}\g@addto@macro\addresses{\par\medskip}%\noindent \br}
    \else\g@addto@macro\addresses{\par\smallskip\medskip\noindent #2\br}\fi
    \fi
  \fi
}
\edef\author{\@nx\@dblarg
  \@xp\@nx\csname\string\author\endcsname}
\let\shortauthors\@empty   \let\authors\@empty
\let\addresses\@empty      \let\thankses\@empty
\newcommand{\address}[2][]{\g@addto@macro\addresses{\address{#1}{#2}}}
\newcommand{\curraddr}[2][]{\g@addto@macro\addresses{\curraddr{#1}{#2}}}
\newcommand{\email}[2][]{\g@addto@macro\addresses{\email{#1}{#2}}}
\newcommand{\twoemails}[3][]{\g@addto@macro\addresses{\twoemails{#1}{#2}{#3}}}
\newcommand{\threeemails}[4][]{\g@addto@macro\addresses{\threeemails{#1}{#2}{#3}{#4}}}
\newcommand{\fouremails}[5][]{\g@addto@macro\addresses{\fouremails{#1}{#2}{#3}{#4}{#5}}}
\newcommand{\fiveemails}[6][]{\g@addto@macro\addresses{\fiveemails{#1}{#2}{#3}{#4}{#5}{#6}}}
\newcommand{\urladdr}[2][]{\g@addto@macro\addresses{\urladdr{#1}{#2}}}
\renewcommand{\thanks}[1]{\g@addto@macro\thankses{\thanks{#1}}}

\newif\ifwritetoc
\writetocfalse

\def\enddoc@text{\ifx\@empty\@translators \else\@settranslators\fi
  \ifx\@empty\addresses \else\@setaddresses\fi
  \ifwritetoc\vfill\eject\tableofcontents\fi}

\AtEndDocument{\enddoc@text}
\def\@setaddresses{\par
  \nobreak \begingroup\small
  \ifADM@
  \scshape
  \parskip0mm
  \else
  \relax
  \fi
%%\footnotesize
%  \def\author##1{\nobreak\addvspace\bigskipamount}%
%  \def\\{\unskip, \ignorespaces}%
  \interlinepenalty\@M
  \def\address##1##2{\begingroup
  \ifADM@
  \upshape
  \else
  \relax
  \fi
%   \par\addvspace\bigskipamount
 \noindent
    \@ifnotempty{##1}{(\ignorespaces##1\unskip) }%
    {\ignorespaces##2}\par\endgroup}%
  \def\curraddr##1##2{\begingroup
    \@ifnotempty{##2}{\nobreak\indent{\upshape Current address}%
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}\/:\space
      ##2\par\endgroup}}%
  \def\email##1##2{\begingroup
    \@ifnotempty{##2}{\nobreak\noindent{\upshape e-mail}%
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}\/:\space
      \upshape\ttfamily##2\par\endgroup}}%
  \def\twoemails##1##2##3{\begingroup
    \@ifnotempty{##2}{\nobreak\noindent{\upshape e-mail}%
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}\/:\space
      \upshape\ttfamily##2\par
      \noindent\hspace*{1.07cm}\upshape\ttfamily##3\par\endgroup}}%
  \def\threeemails##1##2##3##4{\begingroup
    \@ifnotempty{##2}{\nobreak\noindent{\upshape e-mail}%
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}\/:\space
      \upshape\ttfamily##2\par
      \noindent\hspace*{1.07cm}\upshape\ttfamily##3\par
      \noindent\hspace*{1.07cm}\upshape\ttfamily##4\par\endgroup}}%
  \def\fouremails##1##2##3##4##5{\begingroup
    \@ifnotempty{##2}{\nobreak\noindent{\upshape e-mail}%
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}\/:\space
      \upshape\ttfamily##2\par
      \noindent\hspace*{1.07cm}\upshape\ttfamily##3\par
      \noindent\hspace*{1.07cm}\upshape\ttfamily##4\par
      \noindent\hspace*{1.07cm}\upshape\ttfamily##5\par\endgroup}}%
  \def\fiveemails##1##2##3##4##5##6{\begingroup
    \@ifnotempty{##2}{\nobreak\noindent{\upshape e-mail}%
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}\/:\space
      \upshape\ttfamily##2\par
      \noindent\hspace*{1.07cm}\upshape\ttfamily##3\par
      \noindent\hspace*{1.07cm}\upshape\ttfamily##4\par
      \noindent\hspace*{1.07cm}\upshape\ttfamily##5\par
      \noindent\hspace*{1.07cm}\upshape\ttfamily##6\par\endgroup}}%
  \def\urladdr##1##2{\begingroup
    \@ifnotempty{##2}{\nobreak\noindent{\upshape URL}%
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}\/:\space
      \ttfamily##2\par\endgroup}}%
  \addresses
  \endgroup
}
\let\@date\@empty
\def\dedicatory#1{\def\@dedicatory{#1}}
\let\@dedicatory=\@empty
\def\keywords#1{\def\@keywords{#1}}
\let\@keywords=\@empty
\def\subjclass#1{\def\@subjclass{#1}}
%%%%%%%%%%%%%%%%
%\newcommand*\subjclass[2][2000]{%
%  \def\@subjclass{#2}%
%  \@ifundefined{subjclassname@#1}{%
%    \ClassWarning{\@classname}{Unknown edition (#1) of Mathematics
%      Subject Classification; using '1991'.}%
%  }{%
%    \@xp\let\@xp\subjclassname\csname subjclassname@#1\endcsname
%  }%
%}
%%%%%%%%%%%%%%%
\let\@subjclass=\@empty
%\def\commby#1{\def\@commby{(Communicated by #1)}}
%\let\@commby=\@empty
\def\translator#1{%
  \ifx\@empty\@translators \def\@translators{#1}%
  \else\g@addto@macro\@translators{\and#1}\fi}
\let\@translators=\@empty
\def\@settranslators{\par\begingroup
  \addvspace{6\p@\@plus9\p@}%
  \hbox to\columnwidth{\hss\normalfont\normalsize
    Translated by %
    \andify\@translators \uppercasenonmath\@translators
    \@translators}
  \endgroup
}
\newcommand{\xandlist}[4]{\@andlista{{#1}{#2}{#3}}#4\and\and}
\def\@andlista#1#2\and#3\and{\@andlistc{#2}\@ifnotempty{#3}{%
  \@andlistb#1{#3}}}
\def\@andlistb#1#2#3#4#5\and{%
  \@ifempty{#5}{%
    \@andlistc{#2#4}%
  }{%
    \@andlistc{#1#4}\@andlistb{#1}{#3}{#3}{#5}%
  }}
\let\@andlistc\@iden
\newcommand{\nxandlist}[4]{%
  \def\@andlistc##1{\toks@\@xp{\the\toks@##1}}%
  \toks@{\toks@\@emptytoks \@andlista{{#1}{#2}{#3}}}%
  \the\@xp\toks@#4\and\and
  \edef#4{\the\toks@}%
  \let\@andlistc\@iden}
\newcommand{\andify}{%
  \nxandlist{\unskip, }{\unskip{} and~}{\unskip ~and~}}
\def\and{\unskip{ }and \ignorespaces}
\def\maketitle{\par
  \@topnum\z@ % this prevents figures from falling at the top of page 1
  \@setcopyright
%%  \uppercasenonmath\shorttitle
  \ifx\@empty\shortauthors \let\shortauthors\shorttitle
  \else \andify\shortauthors %%\uppercasenonmath\shortauthors
  \fi
  \@maketitle@hook
  \ifADM@
  \begingroup
  \@maketitle
  \toks@\@xp{\sc\shortauthors}
  \@temptokena\@xp{\shorttitle}%
  \edef\@tempa{\@nx\markboth{\the\toks@}{\the\@temptokena}}\@tempa
  \endgroup
  \else
  \begingroup
  \@maketitle
  \toks@\@xp{\shortauthors}
  \@temptokena\@xp{\shorttitle}%
  \edef\@tempa{\@nx\markboth{\the\toks@}{\the\@temptokena}}\@tempa
  \endgroup
  \fi
%  \thispagestyle{firstpage}% this sets first page specifications--->Gerd
  \c@footnote\z@
  \def\do##1{\let##1\relax}%
  \do\maketitle \do\@maketitle \do\title \do\@xtitle \do\@title
  \do\author \do\@xauthor \do\address \do\@xaddress
  \do\email \do\@xemail \do\curraddr \do\@xcurraddr
%  \do\commby \do\@commby
  \do\dedicatory \do\@dedicatory \do\thanks \do\thankses
  \do\keywords \do\@keywords \do\subjclass \do\@subjclass
}
\def\@maketitle@hook{\global\let\@maketitle@hook\@empty}

\newbox\lheadtstbox
\newbox\rheadtstbox

\newdimen\lmaxhead
\newdimen\rmaxhead

\def\@maketitle{%
%%  \normalfont\normalsize
  \let\@makefnmark\relax  \let\@thefnmark\relax
%  \ifx\@empty\@date\else \@footnotetext{\@setdate}\fi
%  \ifx\@empty\@subjclass\else \@footnotetext{\@setsubjclass}\fi
%  \ifx\@empty\@keywords\else \@footnotetext{\@setkeywords}\fi
  \ifx\@empty\thankses\else \@footnotetext{%
    \def\par{\let\par\@par}\@setthanks}\fi
%%%%%%%
%\setbox\lheadtstbox\hbox{\small\shortauthors}%
%\setbox\rheadtstbox\hbox{\small\shorttitle}%
%%%%%%%
  \@mkboth{\@nx\shortauthors}{\@nx\shorttitle}%
  \ifseries@{\global\topskip87\p@\relax }
  \else{\global\topskip87\p@\relax }\fi
  \@settitle
  \ifx\@empty\authors \else \@setauthors \fi
 \ifx\@empty\@dedicatory
  \else
    %%SA \baselineskip21\p@
    \removelastskip\vskip10pt\smallskip
    \vbox{\centering{\footnotesize\itshape\@dedicatory\@@par}%
      \global\dimen@i\prevdepth}\prevdepth\dimen@i
      \vskip10pt\smallskip
    %%SA
  \fi
  \@setabstract
%--------new
  \ifx\@empty\@subjclass \else\@setsubjclass\fi
  \ifx\@empty\@keywords \else\@setkeywords\fi
%--------
  \normalsize
  \if@titlepage
    \newpage
  \else
    \dimen@34\p@ \advance\dimen@-\baselineskip
    \vskip\dimen@\relax
  \fi
} % end \@maketitle
\AtBeginDocument{%
  \@ifundefined{publname}{%
    \let\publname\@empty
    \let\@serieslogo\@empty
  }{%
    \def\@serieslogo{%
      \vbox to\headheight{%
        \parindent\z@ \fontsize{6}{7\p@}\selectfont
        \noindent\publname\newline
        \volinfo, \pageinfo \@dateposted\newline \@PII\endgraf
        \vss
      }%
    }%
  }%
}
\AtBeginDocument{%
  \@ifundefined{volinfo}{%
    \def\volinfo{%
      Volume \currentvolume
    }%
  }{}%
}
%\def\issueinfo#1#2#3#4{\def\currentvolume{#1}\def\currentissue{#2}%
%  \def\currentmonth{#3}\def\currentyear{#4}}
%\issueinfo{00}% volume number
%  {0}%        % issue number
%  {Xxxx}%     % month
%  {XXXX}%     % year
%\def\currentvolume{1}
\def\copyrightinfo#1#2{\def\copyrightyear{#1}\def\copyrightholder{#2}}
\copyrightinfo{0000}{(copyright holder)}
\def\pagespan#1#2{\setcounter{page}{#1}%
  \ifnum\c@page<\z@ \pagenumbering{roman}\setcounter{page}{-#1}\fi
  \def\start@page{#1}\def\end@page{#2}}
\pagespan{000}{000}
\@ifundefined{pageinfo}{%
  \def\pageinfo{%
    \ifnum\start@page=\z@
      Pages 000--000
    \else
      \ifx\start@page\end@page
        Page \start@page
      \else
        Pages \start@page--\end@page
      \fi
    \fi}%
}{}
\@ifundefined{ISSN}{\def\ISSN{0000-0000}}{}
\newcommand\PII[1]{\def\@PII{#1}}
\PII{S \ISSN(XX)0000-0}
\newinsert\copyins
\skip\copyins=1.5pc
\count\copyins=1000 % magnification factor, 1000 = 100%
\dimen\copyins=.5\textheight % maximum allowed per page
\def\@setcopyright{%
  \ifx\@empty\@serieslogo
  \else\ifx\@empty\copyrightyear
  \else
    \insert\copyins{\hsize\textwidth
      \parfillskip\z@ \leftskip\z@\@plus.9\textwidth
      \fontsize{6}{7\p@}\normalfont\upshape
      \everypar{}%
      \vskip-\skip\copyins \nointerlineskip
      \noindent\vrule\@width\z@\@height\skip\copyins
      \copyright\copyrightyear\ \copyrightholder
      \par
      \kern\z@}%
  \fi\fi
}
%----------------------------
\def\issueinfo#1#2#3#4{\def\currentvolume{#1}\def\currentissue{#2}%
  \def\currentmonth{#3}\def\currentyear{#4}}
\issueinfo{00}% volume number
  {0}%        % issue number
  {Xxxx}%     % month
  {XXXX}%     % year
\def\copyrightinfo#1#2{\def\copyrightyear{#1}\def\copyrightholder{#2}}
\copyrightinfo{0000}{(copyright holder)}
\def\pagespan#1#2{\setcounter{page}{#1}%
  \ifnum\c@page<\z@ \pagenumbering{roman}\setcounter{page}{-#1}\fi
  \def\start@page{#1}\def\end@page{#2}}
\pagespan{000}{000}
\@ifundefined{pageinfo}{%
  \def\pageinfo{%
    \ifnum\start@page=\z@
      Pages 000--000
    \else
      \ifx\start@page\end@page
        Page \start@page
      \else
        Pages \start@page--\end@page
      \fi
    \fi}%
}{}
%---also new definitions:
\def\@newref#1{\expandafter\@setref\csname r@#1\endcsname\@firstoftwo{#1}}
\def\@newpageref#1{\expandafter\@setref\csname r@#1\endcsname
                                   \@secondoftwo{#1}}
\def\ref#1{{{\rm\@newref{#1}}}}
\def\pageref#1{{\upshape\@newpageref{#1}}}
%-------------------------
\def\@combinefloats{%
  \ifx \@toplist\@empty \else \@cflt \fi
  \ifx \@botlist\@empty \else \@cflb \fi
  \ifvoid\copyins \else \@cflci \fi
}
\def\@cflci{%
  \if\if@twocolumn \if@firstcolumn F\else T\fi\else T\fi T%
      \setbox\@outputbox\vbox{%
        \unvbox\@outputbox
        \vskip\skip\copyins
        \hbox to\columnwidth{%
          \hss\vbox to\z@{\vss\unvbox\copyins}}}%
  \fi
}
\newcommand{\abstractname}{Abstract}
\newcommand{\keywordsname}{Keywords}
\newcommand{\subjclassname}{Mathematics Subject Classification (2010)}
\def\@tempb{saamsart}

%\ifx\@classname\@tempb
%  \newcommand{\datename}{\textit{Date}:}
%\else
%  \newcommand{\datename}{Received by the editors}
%\fi
%----------------------------
\def\boxr{}
\ifjournal@\font\fxtit=cmssbx10 % For the new logo
\def\xrule{\vrule width2.25pt}
\def\yrule{\hrule height.5pt}
\def\yrulefill{\leaders\yrule\hfill}
\def\strutx{\vrule height8.5pt width0pt depth0pt}
\def\struty{\vrule depth3.5pt width0pt}
\def\strutz{\vrule height11pt width0pt}
\def\boxr{\llap{\vbox to0pt{\vss\vbox{\offinterlineskip
\halign{##\hfil\hskip2mm&##\hfil\hskip2mm\cr
\noalign{\vskip.8mm}
\multispan2{\yrulefill}\cr
\xrule\strutz\struty
&\fxtit \@jourtitle\cr
\ifsecondjournalline@\xrule\strutx&\fxtit \@jourtitlesecond\cr\fi
\noalign{\hrule height0pt}}}}}}\fi


\def\oltext{}

\def\titlesize{\huge}
%\ifjournal@
\def\@settitle{%
\ifADM@
\begingroup%
\baselineskip21pt\relax
\noindent\Large\bfseries
%%\uppercasenonmath\@title
\hbox to0pt{\vbox to0pt{\vss
\begingroup\Small\normalfont\normalbaselines
\noindent\oltext\par\endgroup
\vskip84pt}\hss}
\begin{center}
\@title
\end{center}\par
%\@title\par
\endgroup%
\else
\begingroup%
\baselineskip21pt\relax
\noindent\huge\bfseries
%%\uppercasenonmath\@title
\hbox to0pt{\vbox to0pt{\vss
\begingroup\Small\normalfont\normalbaselines
\noindent\oltext\par\endgroup
\vskip84pt}\hss}\@title\par
%\@title\par
\endgroup
\fi}
%\else\def\@settitle{%
%\begingroup%
%\baselineskip21pt\relax
%\noindent\huge\bfseries
%%\uppercasenonmath\@title
%\hbox to0pt{\vbox to0pt{\vss
%\begingroup\Small\normalfont\normalbaselines
%\noindent\oltext\par\endgroup
%\vskip42pt}\hss}\@title\par
%%\@title\par
%\endgroup}\fi

\newif\ifsignet
\signetfalse

\def\Signet{\signettrue}

\newif\ifmoreinfo
\moreinfofalse


\def\held#1{\def\@held{#1}\global\moreinfotrue}
\let\@held=\@empty
\def\@setheld{{\par\smallskip\noindent\small
\@held\par}}

\def\commby#1{\def\@commby{#1}\global\moreinfotrue}
\let\@commby=\@empty
\def\@setcommby{{\par\smallskip\noindent\small
Communicated by \@commby\@addpunct.\par}}

\def\submitted#1{\def\@submitted{#1}\global\moreinfotrue}
\let\@submitted=\@empty
\def\@setsubmitted{{\par\smallskip\noindent\small
Submitted: \@submitted\@addpunct.\par}}

\def\accepted#1{\def\@accepted{#1}\global\moreinfotrue}
\let\@accepted=\@empty
\def\@setaccepted{{\par\smallskip\noindent\small
Accepted: \@accepted\@addpunct.\par}}

\def\revised#1{\def\@revised{#1}\global\moreinfotrue}
\let\@revised=\@empty
\def\@setrevised{{\par\smallskip\noindent\small
Revised: \@revised\@addpunct.\par}}

\def\received#1{\def\@received{#1}\global\moreinfotrue}
\let\@received=\@empty
\def\@setreceived{{\par\smallskip\noindent\small
Received: \@received\@addpunct.\par}}

\def\translator#1{%
  \ifx\@empty\@translators \def\@translators{#1}%
  \else\g@addto@macro\@translators{\and#1}\fi}
\let\@translators=\@empty
\def\@settranslators{\par\begingroup
  \addvspace{6\p@\@plus9\p@}%
  \hbox to\columnwidth{\hss\normalfont\small
    Translated by %
    \andify\@translators \uppercasenonmath\@translators
    \@translators\@addpunct.}
  \endgroup
}


\def\enddoc@text{\ifnoendauthors@\medskip\else\bigskip\fi
\ifx\@empty\@translators \else\@settranslators\fi
  \ifx\@empty\@addresses \else\@setaddresses\fi
  \ifmoreinfo\par\bigskip\fi
  \ifx\@empty\@held \else\@setheld\fi
  \ifx\@empty\@commby \else\@setcommby\fi
  \ifx\@empty\@submitted \else\@setsubmitted\fi
  \ifx\@empty\@received \else\@setreceived\fi
  \ifx\@empty\@revised \else\@setrevised\fi
  \ifx\@empty\@accepted \else\@setaccepted\fi
  \ifsignet\setsignet\else\fi
  }
 
\def\setsignet{%
\vskip15mm
\begin{center}
%\epsfbox{bvneu.eps}
\includegraphics{bvneu.eps}
\end{center}\par}



%---------------------------
\def\@setauthors{%
  \begingroup
  \trivlist\Large
  \ifADM@
  \centering
  \footnotesize 
  \else
  \raggedright
  \fi
  \@topsep30\p@\relax
  \advance\@topsep by -\baselineskip
  \item\relax
  \andify\authors
%%\uppercasenonmath\authors
\ifADM@
  \sc\authors
  \else
  \authors
  \fi
  \endtrivlist
  \endgroup
%%%%%
  \vskip20pt
%%%%%
}
\def\@setdate{\datename\ \@date\@addpunct.}
\def\@setsubjclass{%
\begin{quote}\small
%\par\addvspace\smallskipamount
%\hangindent=2\parindent\hangafter=1%
%\indent\begingroup\small
{\bfseries\subjclassname.}\ \@subjclass\@addpunct.
\end{quote}}%\par\endgroup}
\def\@setkeywords{%
\begin{quote}\small
%\par\addvspace\smallskipamount
%\hangindent=1\parindent\hangafter=1%
%\indent\begingroup\small
{\bfseries\keywordsname.}\ \@keywords\@addpunct.
\end{quote}}%\par\endgroup}
%{\itshape \keywordsname.}\enspace \@keywords\@addpunct.}
\def\@setthanks{\def\thanks##1{\par##1\@addpunct.}\thankses}
\newbox\abstractbox
\newenvironment{abstract}{%
  \ifx\maketitle\relax
    \ClassWarning{\@classname}{Abstract should precede
      \protect\maketitle\space}%
  \fi
  \global\setbox\abstractbox=\vtop \bgroup
  \normalfont\small
  \small
  \list{}{\labelwidth\z@
    \leftmargin8mm \rightmargin\leftmargin
    \listparindent\normalparindent \itemindent\z@
    \parsep\z@ \@plus\p@
    \let\fullwidthdisplay\relax
    }%
  \item[\hskip\labelsep\bfseries\abstractname.]%
}{%
  \endlist\egroup
  \ifx\@setabstract\relax \@setabstracta \fi
 }
\def\@setabstract{\@setabstracta \global\let\@setabstract\relax}
\def\@setabstracta{%
  \ifvoid\abstractbox
  \else
    %\skip@20\p@ \advance\skip@-\lastskip
    %\advance\skip@-\baselineskip \vskip\skip@
    %\box\abstractbox
%%%%%
\unvbox\abstractbox
%%%%%
\prevdepth\z@ % because \abstractbox is a vtop
\fi
}
\def\titlepage{%
  \clearpage
  \thispagestyle{empty}\setcounter{page}{0}}
\def\endtitlepage{\newpage}
\def\labelenumi{\theenumi.}
\def\theenumi{\@arabic\c@enumi}
\def\labelenumii{(\theenumii)}
\def\theenumii{\@alph\c@enumii}
\def\p@enumii{\theenumi}
\def\labelenumiii{(\theenumiii)}
\def\theenumiii{\@roman\c@enumiii}
\def\p@enumiii{\theenumi(\theenumii)}
\def\labelenumiv{(\theenumiv)}
\def\theenumiv{\@Alph\c@enumiv}
\def\p@enumiv{\p@enumiii\theenumiii}
\def\labelitemi{$\m@th\bullet$}
\def\labelitemii{\bfseries --}% \upshape already done by \itemize
\def\labelitemiii{$\m@th\ast$}
\def\labelitemiv{$\m@th\cdot$}
\newenvironment{verse}{\let\\\@centercr
  \list{}{\itemsep\z@ \itemindent -1.5em\listparindent\itemindent
  \rightmargin\leftmargin \advance\leftmargin 1.5em}\item[]%
}{%
  \endlist
}
\let\endverse=\endlist % for efficiency
\newenvironment{quotation}{\list{}{%
    \leftmargin3pc \listparindent\normalparindent
    \itemindent\z@
    \rightmargin\leftmargin \parsep\z@ \@plus\p@}%
  \item[]%
}{%
  \endlist
}
\let\endquotation=\endlist % for efficiency
\newenvironment{quote}{%
  \list{}{\rightmargin\leftmargin}\item[]%
}{%
  \endlist
}
\let\endquote=\endlist % for efficiency
\def\trivlist{\parsep\parskip\@nmbrlistfalse
  \@trivlist \labelwidth\z@ \leftmargin\z@
  \itemindent\z@
  \let\@itemlabel\@empty
  \def\makelabel##1{\upshape##1}}
\renewenvironment{enumerate}{%
  \ifnum \@enumdepth >3 \@toodeep\else
      \advance\@enumdepth \@ne
      \edef\@enumctr{enum\romannumeral\the\@enumdepth}\list
      {\csname label\@enumctr\endcsname}{\usecounter
        {\@enumctr}\def\makelabel##1{\hss\llap{\upshape##1}}}\fi
}{%
  \endlist
}
\let\endenumerate=\endlist % for efficiency
\renewenvironment{itemize}{%
  \ifnum\@itemdepth>3 \@toodeep
  \else \advance\@itemdepth\@ne
    \edef\@itemitem{labelitem\romannumeral\the\@itemdepth}%
    \list{\csname\@itemitem\endcsname}%
      {\def\makelabel##1{\hss\llap{\upshape##1}}}%
  \fi
}{%
  \endlist
}
\let\enditemize=\endlist % for efficiency
\newcommand{\descriptionlabel}[1]{\hspace\labelsep \upshape\bfseries #1.}
\newenvironment{description}{\list{}{%
  \advance\leftmargini6\p@ \itemindent-12\p@
  \labelwidth\z@ \let\makelabel\descriptionlabel}%
}{
  \endlist
}
\let\enddescription=\endlist % for efficiency
\let\upn=\textup
\AtBeginDocument{%
  \settowidth\leftmargini{\labelenumi\hskip\labelsep}%
  \advance\leftmargini by \normalparindent
  \settowidth\leftmarginii{\labelenumii\hskip\labelsep}%
  \advance\leftmarginii by 6pt
  \settowidth\leftmarginiii{\labelenumiii\hskip\labelsep}%
  \advance\leftmarginiii by 6pt
  \settowidth\leftmarginiv{\labelenumiv\hskip\labelsep}%
  \advance\leftmarginiv by 10pt
  \leftmarginv=10pt
  \leftmarginvi=10pt
  \leftmargin=0pt%\leftmargini
  \labelsep=5pt
  \labelwidth=\leftmargini \advance\labelwidth-\labelsep
  \@listi}
\newskip\listisep
\listisep\smallskipamount
\def\@listI{\leftmargin\normalparindent%\leftmargini 
\parsep\z@skip
  \topsep\listisep \itemsep\z@skip
  \listparindent\normalparindent}
\let\@listi\@listI
\def\@listii{\leftmargin\normalparindent%\leftmarginii
  \labelwidth\leftmarginii \advance\labelwidth-\labelsep
  \topsep\z@skip \parsep\z@skip \partopsep\z@skip \itemsep\z@skip}
\def\@listiii{\leftmargin\normalparindent%leftmarginiii
  \labelwidth\leftmarginiii \advance\labelwidth-\labelsep}
\def\@listiv{\leftmargin\normalparindent%\leftmarginiv
  \labelwidth\leftmarginiv \advance\labelwidth-\labelsep}
\def\@listv{\leftmargin\normalparindent%\leftmarginv
  \labelwidth\leftmarginv \advance\labelwidth-\labelsep}
\def\@listvi{\leftmargin\normalparindent%\leftmarginvi
  \labelwidth\leftmarginvi \advance\labelwidth-\labelsep}
\def\@startsection#1#2#3#4#5#6{%
 \if@noskipsec \leavevmode \fi
 \par \@tempskipa #4\relax
 \@afterindentfalse
 \ifdim \@tempskipa <\z@ \@tempskipa -\@tempskipa \@afterindentfalse\fi
 \if@nobreak \everypar{}\else
     \addpenalty\@secpenalty\addvspace\@tempskipa\fi
 \@ifstar{\@dblarg{\@sect{#1}{\@m}{#3}{#4}{#5}{#6}}}%
         {\@dblarg{\@sect{#1}{#2}{#3}{#4}{#5}{#6}}}%
}
\def\@secnumfont{\bfseries}
\def\@sect#1#2#3#4#5#6[#7]#8{%
  \edef\@toclevel{\ifnum#2=\@m 0\else\number#2\fi}%
  \ifnum #2>\c@secnumdepth \let\@secnumber\@empty
  \else \@xp\let\@xp\@secnumber\csname the#1\endcsname\fi
 \ifnum #2>\c@secnumdepth
   \let\@svsec\@empty
 \else
    \refstepcounter{#1}%
    \edef\@svsec{\ifnum#2<\@m
       \@ifundefined{#1name}{}{%
         \ignorespaces\csname #1name\endcsname\space}\fi
       \@nx\textup{%
      \@nx\@secnumfont
         \csname the#1\endcsname.}\enspace
    }%
  \fi
  \@tempskipa #5\relax
  \ifdim \@tempskipa>\z@ % then this is not a run-in section heading
    \begingroup #6\relax
    \@hangfrom{\hskip #3\relax\@svsec}{\interlinepenalty\@M #8\par}%
    \endgroup
    \ifnum#2>\@m \else \@tocwrite{#1}{#8}\fi
  \else
  \def\@svsechd{#6\hskip #3\@svsec
    \@ifnotempty{#8}{\ignorespaces#8\unskip %}
       \@addpunct.}%
    \ifnum#2>\@m \else \@tocwrite{#1}{#8}\fi
  }%
  \fi
  \global\@nobreaktrue
  \@xsect{#5}}
\let\@ssect\relax
\newcounter{part}
\newcounter{section}
\newcounter{subsection}[section]
\newcounter{subsubsection}[subsection]
\newcounter{paragraph}[subsubsection]
\renewcommand\thepart          {\arabic{part}}
\renewcommand\thesection       {\arabic{section}}
\renewcommand\thesubsection    {\thesection.\arabic{subsection}}
\renewcommand\thesubsubsection {\thesubsection .\arabic{subsubsection}}
\renewcommand\theparagraph     {\thesubsubsection.\arabic{paragraph}}
\setcounter{secnumdepth}{3}
\def\partname{Part}
\def\part{\@startsection{part}{0}%
  \z@{\linespacing\@plus\linespacing}{.5\linespacing}%
  {\normalfont\bfseries\raggedright}}
\def\specialsection{\@startsection{section}{1}%
  \z@{\linespacing\@plus\linespacing}{.5\linespacing}%
  {\normalfont\centering}}
\ifADM@
\def\section{\@startsection{section}{1}%
  \z@{.5\linespacing\@plus.7\linespacing}{-0.5em}%
  {\normalfont\bfseries}}
\def\subsection{\@startsection{subsection}{2}%
  \z@\z@{-\fontdimen2\font}%
  {\normalfont\bfseries}}
\else
\def\section{\@startsection{section}{1}%
  \z@{1.5\linespacing\@plus\linespacing}{.5\linespacing}%
  {\Large\bfseries\raggedright}}
\def\subsection{\@startsection{subsection}{2}%
  \z@{.5\linespacing\@plus.7\linespacing}{.2\linespacing}%
  {\normalfont\bfseries}}
\def\subsubsection{\@startsection{subsubsection}{3}%
  \z@{.5\linespacing\@plus.7\linespacing}{-.5em}%
  {\normalfont\bfseries}}
\def\paragraph{\@startsection{paragraph}{4}%
  \z@\z@{-.5em}%{-\fontdimen2\font}%
  {\normalfont\bfseries}}
\def\subparagraph{\@startsection{subparagraph}{5}%
  \z@\z@{-\fontdimen2\font}%
  \normalfont}
\fi
\def\appendix{\par\c@section\z@ \c@subsection\z@
   \let\sectionname\appendixname
   \def\thesection{\@Alph\c@section}}
\def\appendixname{Appendix}
\def\@Roman#1{\@xp\@slowromancap
  \romannumeral#1@}%
\def\@slowromancap#1{\ifx @#1% then terminate
  \else
    \if i#1I\else\if v#1V\else\if x#1X\else\if l#1L\else\if
    c#1C\else\if m#1M\else#1\fi\fi\fi\fi\fi\fi
    \@xp\@slowromancap
  \fi
}
\newcommand{\@pnumwidth}{1.6em}
\newcommand{\@tocrmarg}{2.6em}
\setcounter{tocdepth}{3}
\def\@starttoc#1#2{\begingroup
  \par\removelastskip\vskip\z@skip
  \@startsection{}\@M\z@{\linespacing\@plus\linespacing}%
    {.5\linespacing}{\centering\upshape}{#2}%
  \ifx\contentsname#2%
  \else \addcontentsline{toc}{section}{#2}\fi
  \makeatletter
  \@input{\jobname.#1}%
  \if@filesw
    \@xp\newwrite\csname tf@#1\endcsname
    \immediate\@xp\openout\csname tf@#1\endcsname \jobname.#1\relax
  \fi
  \global\@nobreakfalse \endgroup
  \addvspace{32\p@\@plus14\p@}%
  \let\tableofcontents\relax
}
\def\contentsname{Contents}
\def\listfigurename{List of Figures}
\def\listtablename{List of Tables}
\def\tableofcontents{\@starttoc{toc}\contentsname}
\def\listoffigures{\@starttoc{lof}\listfigurename}
\def\listoftables{\@starttoc{lot}\listtablename}
\AtBeginDocument{%
  \@for\@tempa:=-1,0,1,2,3\do{%
    \@ifundefined{r@tocindent\@tempa}{%
      \@xp\gdef\csname r@tocindent\@tempa\endcsname{0pt}}{}%
  }%
  \@ifundefined{volinfo}{%
    \def\volinfo{%
      Volume \currentvolume, Number \number0\currentissue,
      \currentmonth\ \currentyear
    }%
  }{}%
\ifADM@\ExecuteOptions{leqno}
\else
\ExecuteOptions{reqno}
\fi
}
\def\@writetocindents{%
  \begingroup
  \@for\@tempa:=-1,0,1,2,3\do{%
    \immediate\write\@auxout{%
      \string\newlabel{tocindent\@tempa}{%
        \csname r@tocindent\@tempa\endcsname}}%
  }%
  \endgroup}
\AtEndDocument{\@writetocindents\if@filesw
\write\@auxout{\string\lastpage{\the\c@page}}\fi
}

\let\indentlabel\@empty
\def\@tochangmeasure#1{\sbox\z@{#1}%
  \ifdim\wd\z@>\csname r@tocindent\@toclevel\endcsname\relax
    \@xp\xdef\csname r@tocindent\@toclevel\endcsname{\the\wd\z@}%
  \fi
}
\def\@toclevel{0}
\def\@tocline#1#2#3#4#5#6#7{\relax
  \ifnum #1>\c@tocdepth % then omit
  \else
    \par \addpenalty\@secpenalty\addvspace{#2}%
    \begingroup \hyphenpenalty\@M
    \@ifempty{#4}{%
      \@tempdima\csname r@tocindent\number#1\endcsname\relax
    }{%
      \@tempdima#4\relax
    }%
    \parindent\z@ \leftskip#3\relax \advance\leftskip\@tempdima\relax
    \rightskip\@pnumwidth plus1em \parfillskip-\@pnumwidth
    #5\leavevmode\hskip-\@tempdima #6\relax
    \hfil\hbox to\@pnumwidth{\@tocpagenum{#7}}\par
    \nobreak
    \endgroup
  \fi}
\def\@tocpagenum#1{\hss{\mdseries #1}}
\def\@tocwrite#1{\@xp\@tocwriteb\csname toc#1\endcsname{#1}}
\def\@tocwriteb#1#2#3{%
  \begingroup
    \def\@tocline##1##2##3##4##5##6{%
      \ifnum##1>\c@tocdepth
      \else \sbox\z@{##5\let\indentlabel\@tochangmeasure##6}\fi}%
    \csname l@#2\endcsname{#1{\csname#2name\endcsname}{\@secnumber}{}}%
  \endgroup
  \addcontentsline{toc}{#2}%
    {\protect#1{\csname#2name\endcsname}{\@secnumber}{#3}}}
\def\l@section{\@tocline{1}{0pt}{1pc}{}{}}
\newcommand{\tocsection}[3]{%
  \indentlabel{\@ifnotempty{#2}{\ignorespaces#1 #2.\quad}}#3}
\def\l@subsection{\@tocline{2}{0pt}{1pc}{5pc}{}}
\let\tocsubsection\tocsection
\def\l@subsubsection{\@tocline{3}{0pt}{1pc}{7pc}{}}
\let\tocsubsubsection\tocsection
\def\l@paragraph{\@tocline{4}{0pt}{1pc}{9pc}{}}
\let\tocparagraph\tocsection
\def\l@part{\@tocline{-1}{12pt plus2pt}{0pt}{}{\bfseries}}
\let\tocpart\tocsection
\def\l@chapter{\@tocline{0}{8pt plus1pt}{0pt}{}{}}
\let\tocchapter\tocsection
\let\tocappendix\tocchapter
\def\l@figure{\@tocline{0}{3pt plus2pt}{0pt}{}{}}
\let\l@table=\l@figure
\def\refname{References}
\def\bibname{Bibliography}
\def\bibliographystyle#1{%
   \if@filesw\immediate\write\@auxout
    {\string\bibstyle{#1}}\fi
        \def\@tempa{#1}%
        \def\@tempb{amsplain}%
        \def\@tempc{}%
        \ifx\@tempa\@tempb
                \def\@biblabel##1{##1.}%
                \def\bibsetup{}%
        \else
                \def\bibsetup{\labelsep6\p@}%
        \ifx\@tempa\@tempc
                \def\@biblabel##1{}%
                \def\bibsetup{\labelwidth\z@ \leftmargin7mm\relax
                \itemindent-7mm\relax
                          \labelsep\z@ }%
        \fi
\fi}
\newenvironment{thebibliography}[1]{%
\ifADM@
  \bigskip
  \@xp\centerline{\textbf{\refname}}%
\else
  \@xp\section\@xp*\@xp{\refname}%
  \fi%
  \normalfont\small%%\footnotesize
  \itemsep=\smallskipamount
  \labelsep3.748\p@\relax%% .5em\relax
  \renewcommand\theenumiv{\arabic{enumiv}}\let\p@enumiv\@empty
  \list{\@biblabel{\theenumiv}}{\settowidth\labelwidth{\@biblabel{#1}}%
    \itemsep=\smallskipamount
    \leftmargin\labelwidth
    \advance\leftmargin\labelsep
    \usecounter{enumiv}}%
  \sloppy \clubpenalty\@M \widowpenalty\clubpenalty
  \sfcode`\.=\@m
}{%
  \def\@noitemerr{\@latex@warning{Empty `thebibliography' environment}}%
  \endlist
}
\def\bysame{\leavevmode\hbox to3em{\hrulefill}\thinspace}
\def\newblock{}
\newcommand\MR[1]{\relax\ifhmode\unskip\spacefactor3000 \space\fi
  \def\@tempa##1:##2:##3\@nil{%
    \ifx @##2\@empty##1\else\textbf{##1:}##2\fi}%
  \MRhref{#1}{MR \@tempa#1:@:\@nil}}
\newcommand\URL{\begingroup
  \def\@sverb##1{%
    \def\@tempa####1##1{\@URL{####1}\egroup\endgroup}%
    \@tempa}%
  \verb}
\let\URLhref\@gobble
\def\@URL#1{\URLhref{#1}#1}
\newif\if@restonecol
\def\theindex{\@restonecoltrue\if@twocolumn\@restonecolfalse\fi
  \columnseprule\z@ \columnsep 35\p@
  \twocolumn[\@xp\section\@xp*\@xp{\indexname}]%
  \thispagestyle{plain}%
  \let\item\@idxitem
  \parindent\z@  \parskip\z@\@plus.3\p@\relax
  \footnotesize}
\def\indexname{Index}
\def\@idxitem{\par\hangindent 2em}
\def\subitem{\par\hangindent 2em\hspace*{1em}}
\def\subsubitem{\par\hangindent 3em\hspace*{2em}}
\def\endtheindex{\if@restonecol\onecolumn\else\clearpage\fi}
\def\indexspace{\par\bigskip}
\def\footnoterule{\kern-.4\p@
        \hrule\@width 5pc\kern11\p@\kern-\footnotesep}
\def\@makefnmark{\hbox{$\m@th^{\@thefnmark}$}}
\def\@makefntext{\noindent\@makefnmark}
\long\def\@footnotetext#1{\insert\footins{%
  \normalfont\footnotesize
  \interlinepenalty\interfootnotelinepenalty
  \splittopskip\footnotesep \splitmaxdepth \dp\strutbox
  \floatingpenalty\@MM \hsize\columnwidth
  \@parboxrestore \parindent\normalparindent \sloppy
  \edef\@currentlabel{\p@footnote\@thefnmark}%
  \@makefntext{\rule\z@\footnotesep\ignorespaces#1\unskip\strut\par}}}
\hfuzz=1pt \vfuzz=\hfuzz
\def\sloppy{\tolerance9999 \emergencystretch 3em\relax}
\setcounter{topnumber}{4}
\setcounter{bottomnumber}{4}
\setcounter{totalnumber}{4}
\setcounter{dbltopnumber}{4}
\renewcommand{\topfraction}{.97}
\renewcommand{\bottomfraction}{.97}
\renewcommand{\textfraction}{.03}
\renewcommand{\floatpagefraction}{.9}
\renewcommand{\dbltopfraction}{.97}
\renewcommand{\dblfloatpagefraction}{.9}
\setlength{\floatsep}{12pt plus 6pt minus 4pt}
\setlength{\textfloatsep}{15pt plus 8pt minus 5pt}
\setlength{\intextsep}{12pt plus 6pt minus 4pt}
\setlength{\dblfloatsep}{12pt plus 6pt minus 4pt}
\setlength{\dbltextfloatsep}{15pt plus 8pt minus 5pt}
\setlength{\@fptop}{0pt}% removed ``plus 1fil''
\setlength{\@fpsep}{8pt}% removed ``plus 2fil''
\setlength{\@fpbot}{0pt plus 1fil}
\setlength{\@dblfptop}{0pt}% removed ``plus 1fil''
\setlength{\@dblfpsep}{8pt}% removed ``plus 2fil''
\setlength{\@dblfpbot}{0pt plus 1fil}
\newcommand{\fps@figure}{tbp}
\newcommand{\fps@table}{tbp}
\newcounter{figure}
\def\@captionheadfont{\scshape}
\def\@captionfont{\normalfont}
\def\ftype@figure{1}
\def\ext@figure{lof}
\def\fnum@figure{\figurename\ \thefigure}
\def\figurename{Figure}
\newenvironment{figure}{%
  \@float{figure}%
}{%
  \end@float
}
\newcounter{table}
\def\ftype@table{2}
\def\ext@table{lot}
\def\fnum@table{\tablename\ \thetable}
\def\tablename{Table}
\newenvironment{table}{%
  \@float{table}%
}{%
  \end@float
}
\def\@floatboxreset{\global\@minipagefalse \centering}
\long\def\@makecaption#1#2{%
  \setbox\@tempboxa\vbox{\color@setgroup
    \advance\hsize-2\captionindent\noindent
    \@captionfont\@captionheadfont#1\@xp\@ifnotempty\@xp
        {\@cdr#2\@nil}{.\@captionfont\upshape\enspace#2}%
    \unskip\kern-2\captionindent\par
    \global\setbox\@ne\lastbox\color@endgroup}%
  \ifhbox\@ne % the normal case
    \setbox\@ne\hbox{\unhbox\@ne\unskip\unskip\unpenalty\unkern}%
  \fi
  \ifdim\wd\@tempboxa=\z@ % this means caption will fit on one line
    \setbox\@ne\hbox to\columnwidth{\hss\kern-2\captionindent\box\@ne\hss}%
  \else % tempboxa contained more than one line
    \setbox\@ne\vbox{\unvbox\@tempboxa\parskip\z@skip
        \noindent\unhbox\@ne\advance\hsize-2\captionindent\par}%
\fi
  \ifnum\@tempcnta<64 % if the float IS a figure...
    \addvspace\abovecaptionskip
    \moveright\captionindent\box\@ne
  \else % if the float IS NOT a figure...
    \moveright\captionindent\box\@ne
    \nobreak
    \vskip\belowcaptionskip
  \fi
\relax
}
\newskip\abovecaptionskip \abovecaptionskip=12pt \relax
\newskip\belowcaptionskip \belowcaptionskip=12pt \relax
\newdimen\captionindent \captionindent=3pc
\RequirePackage{amsthm}[1996/09/24]
\def\@swapped#1#2{#2%
  \@ifnotempty{#1}{\@addpunct{.}\quad#1\unskip}}
\def\thmhead@plain#1#2#3{%
  \thmname{#1}\thmnumber{\@ifnotempty{#1}{ }\@upn{#2}}%
  \thmnote{ \textbf{\upshape(#3)}}}
\def\swappedhead@plain#1#2#3{%
  \thmnumber{\@upn{#2}}\thmname{\@ifnotempty{#2}{. }#1}%
  \thmnote{ \textbf{\upshape(#3)}}}
\def\th@plain{%
  \let\thmhead\thmhead@plain \let\swappedhead\swappedhead@plain
  \thm@preskip.5\baselineskip\@plus.2\baselineskip
                                    \@minus.2\baselineskip
  \thm@postskip\thm@preskip
  \itshape
}
\def\th@definition{%
  \let\thmhead\thmhead@plain \let\swappedhead\swappedhead@plain
  \thm@preskip.5\baselineskip\@plus.2\baselineskip
                                    \@minus.2\baselineskip
  \thm@postskip\thm@preskip
  \upshape
}
\def\th@remark{%
  \thm@headfont{\itshape}% heading font bold
\def\thmhead@plain##1##2##3{%
  \thmname{##1}\thmnumber{\@ifnotempty{##1}{ }\@upn{##2}}%
  \thmnote{ \upshape(##3)}}
\def\swappedhead@plain##1##2##3{%
  \thmnumber{\@upn{##2}}\thmname{\@ifnotempty{##2}{. }##1}%
  \thmnote{ \upshape(##3)}}
  \let\thmhead\thmhead@plain \let\swappedhead\swappedhead@plain
  \thm@preskip.5\baselineskip\@plus.2\baselineskip
                                    \@minus.2\baselineskip
  \thm@postskip\thm@preskip
  \upshape
}
\if@compatibility
\let\@newpf\proof \let\proof\relax \let\endproof\relax
\newenvironment{pf}{\@newpf[\proofname]}{\qed\endtrivlist}
\newenvironment{pf*}[1]{\@newpf[#1]}{\qed\endtrivlist}
\fi
\def\nonbreakingspace{\unskip\nobreak\ \ignorespaces}
\def~{\protect\nonbreakingspace}
\def\@biblabel#1{\@ifnotempty{#1}{[#1]}}
\def\@cite#1#2{{%
  \m@th\upshape\mdseries[{#1\if@tempswa, #2\fi}]}}
\@ifundefined{cite }{%
  \expandafter\let\csname cite \endcsname\cite
  \edef\cite{\@nx\protect\@xp\@nx\csname cite \endcsname}%
}{}
\def\fullwidthdisplay{\displayindent\z@ \displaywidth\columnwidth}
\edef\@tempa{\noexpand\fullwidthdisplay\the\everydisplay}
\everydisplay\expandafter{\@tempa}
\newcommand\seename{see also}%
\newcommand\see[2]{{\em \seename\/} #1}%
\newcommand\printindex{\@input{\jobname.ind}}%
\DeclareRobustCommand\textprime{\leavevmode
  \raise.8ex\hbox{\check@mathfonts\the\scriptfont2 \char48 }}
\hyphenation{acad-e-my acad-e-mies af-ter-thought anom-aly anom-alies
an-ti-deriv-a-tive an-tin-o-my an-tin-o-mies apoth-e-o-ses
apoth-e-o-sis ap-pen-dix ar-che-typ-al as-sign-a-ble as-sist-ant-ship
as-ymp-tot-ic asyn-chro-nous at-trib-uted at-trib-ut-able bank-rupt
bank-rupt-cy bi-dif-fer-en-tial blue-print busier busiest
cat-a-stroph-ic cat-a-stroph-i-cally con-gress cross-hatched data-base
de-fin-i-tive de-riv-a-tive dis-trib-ute dri-ver dri-vers eco-nom-ics
econ-o-mist elit-ist equi-vari-ant ex-quis-ite ex-tra-or-di-nary
flow-chart for-mi-da-ble forth-right friv-o-lous ge-o-des-ic
ge-o-det-ic geo-met-ric griev-ance griev-ous griev-ous-ly
hexa-dec-i-mal ho-lo-no-my ho-mo-thetic ideals idio-syn-crasy
in-fin-ite-ly in-fin-i-tes-i-mal ir-rev-o-ca-ble key-stroke
lam-en-ta-ble light-weight mal-a-prop-ism man-u-script mar-gin-al
meta-bol-ic me-tab-o-lism meta-lan-guage me-trop-o-lis
met-ro-pol-i-tan mi-nut-est mol-e-cule mono-chrome mono-pole
mo-nop-oly mono-spline mo-not-o-nous mul-ti-fac-eted mul-ti-plic-able
non-euclid-ean non-iso-mor-phic non-smooth par-a-digm par-a-bol-ic
pa-rab-o-loid pa-ram-e-trize para-mount pen-ta-gon phe-nom-e-non
post-script pre-am-ble pro-ce-dur-al pro-hib-i-tive pro-hib-i-tive-ly
pseu-do-dif-fer-en-tial pseu-do-fi-nite pseu-do-nym qua-drat-ic
quad-ra-ture qua-si-smooth qua-si-sta-tion-ary qua-si-tri-an-gu-lar
quin-tes-sence quin-tes-sen-tial re-arrange-ment rec-tan-gle
ret-ri-bu-tion retro-fit retro-fit-ted right-eous right-eous-ness
ro-bot ro-bot-ics sched-ul-ing se-mes-ter semi-def-i-nite
semi-ho-mo-thet-ic set-up se-vere-ly side-step sov-er-eign spe-cious
spher-oid spher-oid-al star-tling star-tling-ly sta-tis-tics
sto-chas-tic straight-est strange-ness strat-a-gem strong-hold
sum-ma-ble symp-to-matic syn-chro-nous topo-graph-i-cal tra-vers-a-ble
tra-ver-sal tra-ver-sals treach-ery turn-around un-at-tached
un-err-ing-ly white-space wide-spread wing-spread wretch-ed
wretch-ed-ly Eng-lish Euler-ian Feb-ru-ary Gauss-ian
Hamil-ton-ian Her-mit-ian Jan-u-ary Japan-ese Kor-te-weg
Le-gendre Mar-kov-ian Noe-ther-ian No-vem-ber Rie-mann-ian Sep-tem-ber}
\def\calclayout{\advance\textheight -\headheight
  \advance\textheight -\headsep
  \oddsidemargin\paperwidth
  \advance\oddsidemargin -\textwidth
  \divide\oddsidemargin\tw@
  \ifdim\oddsidemargin<.5truein \oddsidemargin.5truein \fi
  \advance\oddsidemargin 48.65pt%-1truein
  \evensidemargin\oddsidemargin
  \topmargin\paperheight \advance\topmargin -\textheight
  \advance\topmargin -\headheight \advance\topmargin -\headsep
  \divide\topmargin\tw@
  \ifdim\topmargin<.5truein \topmargin.5truein \fi
  \advance\topmargin 48.65pt\relax%-1truein\relax
}
\calclayout % initialize

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                %%
%% Some more handy definitions                    %%
%%                                                %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\ifteinsformat@\relax\else
\setlength{\textwidth}{125mm}
\setlength{\textheight}{185mm}\fi
%\setlength{\parindent}{8mm}
\ifADM@
\parskip=5pt plus1pt minus2pt\relax
\setlength{\parindent}{5mm}
\else
\parskip=0pt plus1pt\relax
\setlength{\parindent}{8mm}
\fi
\ifADM@\ExecuteOptions{leqno}  \tagsleft@true \PassOptionsToPackage{leqno}{amsmath}
\else
\fi
\frenchspacing
\ifteinsformat@\relax\else\setlength{\oddsidemargin}{48.65pt}
\setlength{\evensidemargin}{48.65pt}
\setlength{\topmargin}{48.65pt}\fi

\gdef\bfdefault{b}

\newcommand{\pdpg}{\postdisplaypenalty=-5000}
\newcommand{\pdpb}{\postdisplaypenalty=10000}
\newcommand{\matheject}{\postdisplaypenalty=-10000}

\newcommand{\br}{\hfill\break}
\newcommand{\phn}{\phantom{0}}

\newcommand{\pbox}[1]{\hbox to\parindent{\hfil#1}}

\renewcommand\qedsymbol{\ifmmode\square\else$\square$\fi}

\newcounter{firstpage}
\newcounter{lastpage}
\newcounter{nrofpages}
\setcounter{firstpage}{1}
\setcounter{lastpage}{0}
\setcounter{nrofpages}{0}

\newcommand\@firstpage{000}
\newcommand\@lastpage{000}
\newcommand\@nrissue{00}
\newcommand\@volyear{00 (0000)}
\newcommand\@DOI{003-0000}

%%\def\oltext{}

\newcommand\firstpage[1]{%
\global\setcounter{page}{#1}
\global\setcounter{firstpage}{#1}}

\gdef\@SAdummy{\csname arabic\endcsname}

\newcommand\@adjustcounters{%
\global\setcounter{lastpage}{\@lastpage}%
\global\setcounter{nrofpages}{\@lastpage}%
\addtocounter{nrofpages}{1}%
\addtocounter{nrofpages}{-\thefirstpage}%
\ifx\actualnumberingstyle\@SAdummy
\ifnum \thefirstpage<10%
\xdef\@firstpage{000\thefirstpage}\else%
\ifnum \thefirstpage<100%
\xdef\@firstpage{00\thefirstpage}\else%
\ifnum \thefirstpage<1000%
\xdef\@firstpage{0\thefirstpage}\else%
\ifnum \thefirstpage<10000%
\xdef\@firstpage{\thefirstpage}\else%
\errormessage{First pagenumber too big!!}\fi\fi\fi\fi\fi}

\newcommand\lastpage[1]{\xdef\@lastpage{#1}%
\global\setcounter{lastpage}{\@lastpage}}

\ifseries@\renewcommand\oltext{%
\ifseriesextraline@{\@seriesextraline\smallskip\br}\fi
\se@ies\ifjournal@\ \@volyear\fi
\ifseriesextra@{:\ \textit{\@seriesextra}}\fi,%
\ifvolume@{\ Vol. \@volume, }\else\ \fi
\@adjustcounters
\message{%
**************************^^J%
*\space\space\space\space\space\space
\space first page: \the\c@firstpage^^J%
*\space\space\space\space\space\space\space
\space last page: \the\c@lastpage^^J%
*\space\space\space\space\space no. of pages: \the\c@nrofpages^^J%
*\space\space\space\space pagenumbering: \actualnumberingstyletext^^J%
%*\space\space left head width: \ifdim\wd\lheadtstbox<\lmaxhead OK
%\else too long!\fi ^^J%
%*\space right head width: \ifdim\wd\rheadtstbox<\rmaxhead OK
%\else too long!\fi ^^J%
**************************^^J}
\ifnum\thenrofpages>1
\actualnumberingstyle{firstpage}--%
\actualnumberingstyle{lastpage}\br
\else \actualnumberingstyle{firstpage}\br\fi
%\thefirstpage--\@lastpage\br
\ifMJM@\relax\else
\fi
\ifDOI@{DOI 10.1007/\@DOInr-\@DOI\ \br}\fi
\copyright\ \@cpyear\ Birkh\"auser 
Verlag Basel/Switzerland\hfill\boxr\par}\fi

\ifonlinefirst@
\renewcommand\oltext{%
\@adjustcounters
\message{%
**************************^^J%
*\space\space\space\space\space\space
\space first page: \the\c@firstpage^^J%
*\space\space\space\space\space\space\space
\space last page: \the\c@lastpage^^J%
*\space\space\space\space\space no. of pages: \the\c@nrofpages^^J%
*\space\space\space\space pagenumbering: \actualnumberingstyletext^^J%
*\space\space left head width: \ifdim\wd\lheadtstbox<\lmaxhead OK 
\else too long!\fi ^^J%
*\space right head width: \ifdim\wd\rheadtstbox<\rmaxhead OK
\else too long!\fi ^^J%
**************************^^J}%
\ifMJM@\relax\else
\ifseriesextraline@{\@seriesextraline\smallskip\br}\fi \se@ies\ \
\textit{Online First}\ifseriesextra@{:\
\textit{\@seriesextra}}\fi\br \copyright\ \@cpyear\ Birkh\"auser
Verlag Basel/Switzerland\br
DOI 10.1007/\@DOInr-\@DOI\hfill\boxr\par\fi}
\def\@oddhead{\normalfont\ifjournal@\small\ \fi\hfil
\rightmark{}{}\hfil \llap{\thepage}}%
\fi
\ifprintsecond@\renewcommand\oltext{%
\ifseriesextraline@{\@seriesextraline\smallskip\br}\fi
\se@ies\ifjournal@\ \@volyear\fi\ifseriesextra@{:\ \textit{\@seriesextra}}\fi,\ifvolume@{\ Vol. \@volume, }\else\ \fi
\@adjustcounters
\message{%
**************************^^J%
*\space\space\space\space\space\space
\space first page: \the\c@firstpage^^J%
*\space\space\space\space\space\space\space
\space last page: \the\c@lastpage^^J%
*\space\space\space\space\space no. of pages: \the\c@nrofpages^^J%
*\space\space\space\space pagenumbering: \actualnumberingstyletext^^J%
*\space\space left head width: \ifdim\wd\lheadtstbox<\lmaxhead OK
\else too long!\fi ^^J%
*\space right head width: \ifdim\wd\rheadtstbox<\rmaxhead OK
\else too long!\fi ^^J%
**************************^^J}
\ifnum\thenrofpages>1
\actualnumberingstyle{firstpage}--%
\actualnumberingstyle{lastpage}\br
\else \actualnumberingstyle{firstpage}\br\fi
%\thefirstpage--\@lastpage\br
\copyright\ \@cpyear\ Birkh\"auser Verlag Basel/Switzerland\br
\ifjournal@\textit{Published online}\! \@onlinedate\fi\br
DOI 10.1007/\@DOInr-\@DOI\hfill\boxr\par}\fi
\ifteinsformat@\usepackage[paperwidth=155mm,paperheight=235mm,tmargin=21mm,lmargin=19mm,rmargin=19mm,bmargin=21mm,asymmetric]{geometry}
\special{papersize=15.5cm,23.5cm}\RequirePackage{amsmath}
\fi


\newcommand\issuenumber[1]{%
\ifnum #1<10\renewcommand\@nrissue{0#1}\else
\renewcommand\@nrissue{#1}\fi}
\issuenumber{99}
\newcommand\Volumeandyear[1]{\def\@volyear{#1}}
\Volumeandyear{99 (9999)}
\newcommand\DOI[1]{\def\@DOI{#1}}
\DOI{003-0000}
\newcommand\Copyrightyear[1]{\def\@cpyear{#1}}
\Copyrightyear{\the\year}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\def\pagenumbering#1{%
\xdef\actualnumberingstyletext{#1}%
\gdef\actualnumberingstyle{\csname #1\endcsname }%
\global\c@page \@ne 
\gdef\thepage{\csname @#1\endcsname \c@page}}

\global\lmaxhead=.8\textwidth
\global\rmaxhead=\lmaxhead

\pagenumbering{arabic}
\pagestyle{headings}
\thispagestyle{empty}
\if@compatibility \else\endinput\fi
\def\tiny{\Tiny}
\def\defaultfont{\normalfont}
\def\rom{\textup}


\endinput
%%
%% End of file `birkmult.cls'. 
