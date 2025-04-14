# Placeholders for built-in symbols
module Fw {
  port BufferSend
  port Cmd
  port CmdReg
  port CmdResponse
  port DpGet
  port DpRequest
  port DpResponse
  port DpSend
  port Log
  port LogText
  port PrmGet
  port PrmSet
  port Time
  port Tlm
}

module Svc {
  port Ping
  port Sched
  passive component Time {

  }
}
