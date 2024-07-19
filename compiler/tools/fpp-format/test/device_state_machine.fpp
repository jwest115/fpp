@ Fault data
struct FaultData {
  $id: U32
  data: U32
}

@ Power data
struct PowerData {
  level: F32
}
@ Device state machine
state machine Device {

  # ---------------------------------------------------------------------- 
  # Signals
  # ---------------------------------------------------------------------- 

  @ RTI signal
  signal RTI

  @ Complete signal
  signal Complete

  @ Calibrate signal
  signal Calibrate

  @ Fault signal
  signal Fault: FaultData

  @ Drive signal
  signal Drive

  @ Stop signal
  signal Stop

  @ Resume signal
  signal Resume

  @ POR signal
  signal POR

  @ Power on signal
  signal PowerOn: PowerData

  @ Power off signal
  signal PowerOff

  # ---------------------------------------------------------------------- 
  # Actions
  # ---------------------------------------------------------------------- 

  @ Action a1
  action a1

  @ Action init1
  action init1

  @ Action init2
  action init2

  @ Action set power
  action setPower: PowerData

  @ Action init power
  action initPower

  @ Action report fault
  action reportFault: FaultData

  @ Action motor control
  action motorControl

  @ Action do calibrate
  action doCalibrate

  @ Action do safe
  action doSafe

  @ Action do diagnostics
  action doDiagnostics

  # ---------------------------------------------------------------------- 
  # Guards
  # ---------------------------------------------------------------------- 

  @ Cold start guard
  guard coldStart

  @ No recovery guard
  guard noRecovery: FaultData

  @ Calibrate ready guard
  guard calibrateReady

  # ---------------------------------------------------------------------- 
  # States and junctions
  # ---------------------------------------------------------------------- 

  @ Initial transition
  initial do init1 enter j1

  @ Junction j1
  junction j1 {
    if coldStart do a1 enter DEVICE_OFF \
    else do initPower enter DEVICE_ON
  }

  @ DEVICE_OFF state
  state DEVICE_OFF {
    on PowerOn do setPower enter DEVICE_ON
  }

  @ DEVICE_ON state
  state DEVICE_ON {

    @ Initial transition
    initial do init2 enter INITIALIZING

    @ INITIALIZING state
    state INITIALIZING {
      on Complete enter IDLE
    }

    @ IDLE state
    state IDLE {
      on Drive enter DRIVING
      on Calibrate if calibrateReady enter CALIBRATING
    }

    @ CALIBRATING state
    state CALIBRATING {
      on RTI do doCalibrate
      on Fault do reportFault enter IDLE
      on Complete enter IDLE
    }

    @ DRIVING state
    state DRIVING {
      on RTI do motorControl
      on Stop enter IDLE
    }

    @ Transition to DEVICE_ON
    on POR enter DEVICE_ON

    @ Transition to j2
    on Fault enter j2

    @ Transition to DEVICE_OFF
    on PowerOff enter DEVICE_OFF
  }

  @ Junction j2
  junction j2 {
    if noRecovery enter DIAGNOSTICS \
    else do reportFault enter RECOVERY
  }

  @ RECOVERY state
  state RECOVERY {
    on RTI do doSafe
    on Complete enter DIAGNOSTICS
  }

  @ DIAGNOSTICS state
  state DIAGNOSTICS {
    on RTI do doDiagnostics
    on Resume enter DEVICE_ON
  }

}
