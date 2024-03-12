if exists("b:current_syntax")
	finish
endif

syntax keyword eqlogTodo contained TODO FIXME XXX NB NOTE
highlight default link eqlogTodo Todo

syntax region eqlogComment start="//" end="$" contains=eqlogTodo,@Spell
highlight default link eqlogComment Comment

syntax match eqlogIdentifier "\%([^[:cntrl:][:space:][:punct:][:digit:]]\|_\)\%([^[:cntrl:][:punct:][:space:]]\|_\)*" display contained
highlight default link eqlogIdentifier Identifier

syntax match eqlogOperator "=\|!\|->"
highlight default link eqlogOperator Operator

syntax keyword eqlogDecl
  \ type
  \ pred
  \ func
  \ rule
  \ nextgroup=eqlogIdentifier skipwhite skipempty
highlight default link eqlogDecl Keyword

syntax keyword eqlogConditional
  \ if
  \ then
  \ branch
  \ along
highlight default link eqlogConditional Conditional

let b:current_syntax = "eqlog"
