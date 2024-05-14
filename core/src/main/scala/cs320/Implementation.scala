package cs320

import Value._

object Implementation extends Template {

  case class ExceptionHandler(take : Option[(Expr, Env, Cont, ExceptionHandler)])

  def interp(expr: Expr): Value = interpreter(expr, Map(), ExceptionHandler(None), damn => damn)

  def interpreter(expr: Expr, env: Env, hand: ExceptionHandler, k: Cont): Value = expr match {
    case Id(x) => k(env.getOrElse(x, error()))

    case IntE(v) => k(IntV(v))

    case BooleanE(v) => v match {
      case true => k(BooleanV(true))
      case false => k(BooleanV(false))
      case _ => error()
    }

    case Add(l, r) => 
      interpreter(l, env, hand, v1 =>
        interpreter(r, env, hand, v2 => 
          v1 match {
            case IntV(n) => {
              v2 match {
                case IntV(m) => k(IntV(n + m))
                case _ => error()
              }
            }
            case _ => error()
          }))
    
    case Mul(l, r) => 
      interpreter(l, env, hand, v1 =>
        interpreter(r, env, hand, v2 => 
          v1 match {
            case IntV(n) => {
              v2 match {
                case IntV(m) => k(IntV(m*n))
                case _ => error()
              }
            }
            case _ => error()
          }))
    
    case Div(l, r) =>
      interpreter(l, env, hand, v1 =>
        interpreter(r, env, hand, v2 =>
          v1 match {
            case IntV(n) => {
              v2 match {
                case IntV(m) => {
                  if(m == 0){
                    error()
                  }else{
                    k(IntV(n/m))
                  }
                }
                case _ => error()
              }
            }
            case _ => error()
          }))

    case Mod(l, r) =>
      interpreter(l, env, hand, v1 =>
        interpreter(r, env, hand, v2 =>
          v1 match {
            case IntV(n) => {
              v2 match {
                case IntV(m) => {
                  if(m == 0){
                    error()
                  }else{
                    k(IntV(n%m))
                  }
                }
                case _ => error()
              }
            }
            case _ => error()
          }))
    
    case Eq(l, r) =>
      interpreter(l, env, hand, v1 =>
        interpreter(r, env, hand, v2 =>
          v1 match {
            case IntV(n) => {
              v2 match {
                case IntV(m) => {
                  if(n == m){
                    k(BooleanV(true))
                  }else{
                    k(BooleanV(false))
                  }
                }
                case _ => error()
              }
            }
            case _ => error()
          }))

    case Lt(l, r) =>
      interpreter(l, env, hand, v1 =>
        interpreter(r, env, hand, v2 =>
          v1 match {
            case IntV(n) => {
              v2 match {
                case IntV(m) => {
                  if(n < m){
                    k(BooleanV(true))
                  }else{
                    k(BooleanV(false))
                  }
                }
                case _ => error()
              }
            }
            case _ => error()
          }))


    case If(condition, t, f) => {
      interpreter(condition, env, hand, res =>
        res match {
          case BooleanV(true) => {
            interpreter(t, env, hand, k)
          }
          case BooleanV(false) => {
            interpreter(f, env, hand, k)
          }
          case _ => error()
        })
    }

    
    // case TupleE(expressions) => {
    //   val x = expressions.map((e) => interpreter(e, env, k))
    //   k(TupleV(x))
    //   // TupleV(x)
    // }

    case TupleE(expressions) => expressions match {
      case Nil => k(TupleV(Nil))
      case h::t => interpreter(h, env, hand, hv => interpreter(TupleE(t), env, hand, tv => tv match {
        case TupleV(sth) => k(TupleV(hv::sth))
        case _ => error()
      }))
    }

    case Proj(e, index) => {
      interpreter(e, env, hand, a =>
        a match {
          case TupleV(ans) => {
            if(1 <= index && index <= ans.length){
              k(ans(index-1))
              // ans(index - 1)
            }else{
              error()
            }
          }
          case _ => error()
        })
    }

    case NilE => k(NilV)

    case ConsE(h, t) => {
      interpreter(h, env, hand, v1 =>
        interpreter(t, env, hand, v2 =>
          v2 match {
            case NilV => k(ConsV(v1, v2))
            case ConsV(head, tail) => k(ConsV(v1, v2))
            case _ => error()
          }))
    }

    case Empty(e) => {
      interpreter(e, env, hand, ans =>
        ans match {
          case NilV => k(BooleanV(true))
          case ConsV(head, tail) => k(BooleanV(false))
          case _ => error()
        })
    }

    case Head(e) => {
      interpreter(e, env, hand, x => 
        x match {
          case ConsV(head, tail) => k(head)
          case _ => error()
        })
    }

    case Tail(e) => {
      interpreter(e, env, hand, x =>
        x match {
          case ConsV(head, tail) => k(tail)
          case _ => error()
        })
    }

    case Val(name, e, body) => {
      interpreter(e, env, hand, v1 =>
        interpreter(body, env + (name -> v1), hand, v2 =>
          k(v2)))
    }

    case Vcc(name, body) => {
      interpreter(body, env + (name -> ContV(k)), hand, k)
    }

    case Fun(para, body) => {
      k(CloV(para, body, env))
    }

    case RecFuns(functions, body) => {
      val vv = functions.map((f) => CloV(f.parameters, f.body, env))
      val v_name = functions.map((f) => f.name)
      val mp = (v_name zip vv).toMap
      vv.foreach((clo) => {clo.env = env ++ mp})
      interpreter(body, env ++ mp, hand, k)
    }

    case App(function, arguments) => {
      interpreter(function, env, hand, fv => {
        interpreter(TupleE(arguments), env, hand, artuple => {
          artuple match {
            case TupleV(av) => fv match {
              case CloV(parameters, body, nenv) => {
                if(parameters.length != av.length){
                  error()
                }else{
                  interpreter(body, nenv ++ (parameters zip av).toMap, hand, k)
                }
              }
              case ContV(nk) => {
                if(av.length == 1){
                  nk(av(0))
                }else{
                  error()
                }
              }
              case _ => error()
            }
            case _ => error()
          }
        })
      })
    }

    case Test(e, typ) => {
      interpreter(e, env, hand, v =>
        v match {
          case IntV(value) => {
            typ match {
              case IntT => k(BooleanV(true))
              case _ => k(BooleanV(false))
            }
          }
          case BooleanV(value) => {
            typ match {
              case BooleanT => k(BooleanV(true))
              case _ => k(BooleanV(false))
            }
          }
          case TupleV(value) => {
            typ match {
              case TupleT => k(BooleanV(true))
              case _ => k(BooleanV(false))
            }
          }
          case NilV => {
            typ match {
              case ListT => k(BooleanV(true))
              case _ => k(BooleanV(false))
            }
          }
          case ConsV(head, tail) => {
            typ match {
              case ListT => k(BooleanV(true))
              case _ => k(BooleanV(false))
            }
          }
          case CloV(parameters, body, env) => {
            typ match {
              case FunctionT => k(BooleanV(true))
              case _ => k(BooleanV(false))
            }
          }
          case ContV(continuation) => {
            typ match {
              case FunctionT => k(BooleanV(true))
              case _ => k(BooleanV(false))
            }
          }
          case _ => error()
        })
    }

    case Throw(e) => interpreter(e, env, hand, evalue => {
      hand.take match {
        case Some((hexpr, henv, hk, hhand)) => interpreter(hexpr, henv, hhand, hexprv => hexprv match {
          case ContV(x) => x(evalue)
          case CloV(parameters, body, fenv) => parameters match {
            case a::Nil => interpreter(body, fenv + (a -> evalue), hhand, hk)
            case _ => error()
          }
          case _ => error()
        })
        case _ => error()
      }
    })

    case Try(expr1, expr2) => {
      val h_new = ExceptionHandler(Some(expr2, env, k, hand))
      interpreter(expr1, env, h_new, k)
    }

    case _ => error()

  }

}
