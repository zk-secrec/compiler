" Vim syntax file
" Language:		ZKSC
" Maintainer:   Joosep Jääger

if exists("b:current_syntax")
  finish
endif

syn keyword zkscKeyword    pub sieve extern for in if else rec as witness break continue default let true false mut ref where wire post while unchecked eff forall zip with
syn keyword zkscKeyword    struct impl fn type nextgroup=zkscIdentifier skipwhite skipempty
syn keyword zkscBuiltinFun dbg_print dbg_assert get_instance get_witness get_public challenge assert assert_zero length
syn keyword zkscPreProc    use
syn keyword zkscType       uint bool string list arr tuple store Domain Nat Qualified Stage unit Unqualified

syn match zkscIdentifier '\w\+' nextgroup=zkscType display contained
syn match zkscComment    '//.*$'
syn match zkscStage      '\$[A-Z]\w*'
syn match zkscStage      '\$pre'
syn match zkscStage      '\$post'
syn match zkscDomain     '@[A-Z]'
syn match zkscDomain     '@public'
syn match zkscDomain     '@prover'
syn match zkscDomain     '@verifier'
syn match zkscNumber     '\<[0-9]\+'
syn match zkscNumber     '0x[0-9a-fA-F]\+'
syn match zkscFixity     'infix[lr]\?'

syn region zkscString start='"' end='"'
syn region zkscBlockComment start='/\*' end='\*/'

hi def link zkscKeyword      Statement
hi def link zkscBuiltinFun   Statement
hi def link zkscType         Type
hi def link zkscStage        Type
hi def link zkscDomain       Type
hi def link zkscFixity       Type
hi def link zkscPreproc      PreProc
hi def link zkscNumber       Number
hi def link zkscString       String
hi def link zkscComment      Comment
hi def link zkscBlockComment Comment
hi def link zkscIdentifier   Identifier

let b:current_syntax = "zksc"
