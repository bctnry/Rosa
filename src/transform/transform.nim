import ../ast
import lambdalifting

proc transform*(x: Program): Program =
  var subj = x
  subj = subj.lambdaLifting
  return subj
  
