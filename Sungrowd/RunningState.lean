namespace Sungrowd

/-- Register 12999, "running state" (older docs: "system state"). The codes and labels are the
`Sungrow inverter state` template in `reference/modbus_sungrow.yaml`.

The table is a lookup of exact values, not bit flags. It mixes two numberings, so several
labels appear twice (e.g. "Stop" is both 0x0001 and 0x8000); those constructors carry the
code as a suffix so that every code keeps its own constructor and `toRaw` is injective. -/
inductive RunningState
  | running0000
  | stop0001
  | keyStop0002
  | emergencyStop0004
  | standby0008
  | initialStandby0010
  | microgridOperation
  | starting0020
  | running0040
  | offGridCharge
  | deratingRunning0080
  | fault0100
  | updateFailed
  | maintainMode
  | forcedMode
  | runningOffGrid
  | uninitialized
  | initialStandby1200
  | keyStop1300
  | standby1400
  | emergencyStop1500
  | starting1600
  | afciSelfTestShutdown
  | intelligentStationBuilding
  | safeMode
  | openLoop
  | communicateFault
  | restarting
  | externalEMSMode
  | emergencyCharging
  | fault5500
  | stop8000
  | deratingRunning8100
  | dispatchRunning
  | warnRunning
  deriving DecidableEq, Repr

def RunningState.toRaw : RunningState → UInt16
  | .running0000                => 0x0000
  | .stop0001                   => 0x0001
  | .keyStop0002                => 0x0002
  | .emergencyStop0004          => 0x0004
  | .standby0008                => 0x0008
  | .initialStandby0010         => 0x0010
  | .microgridOperation         => 0x0014
  | .starting0020               => 0x0020
  | .running0040                => 0x0040
  | .offGridCharge              => 0x0041
  | .deratingRunning0080        => 0x0080
  | .fault0100                  => 0x0100
  | .updateFailed               => 0x0200
  | .maintainMode               => 0x0400
  | .forcedMode                 => 0x0800
  | .runningOffGrid             => 0x1000
  | .uninitialized              => 0x1111
  | .initialStandby1200         => 0x1200
  | .keyStop1300                => 0x1300
  | .standby1400                => 0x1400
  | .emergencyStop1500          => 0x1500
  | .starting1600               => 0x1600
  | .afciSelfTestShutdown       => 0x1700
  | .intelligentStationBuilding => 0x1800
  | .safeMode                   => 0x1900
  | .openLoop                   => 0x2000
  | .communicateFault           => 0x2500
  | .restarting                 => 0x2501
  | .externalEMSMode            => 0x4000
  | .emergencyCharging          => 0x4001
  | .fault5500                  => 0x5500
  | .stop8000                   => 0x8000
  | .deratingRunning8100        => 0x8100
  | .dispatchRunning            => 0x8200
  | .warnRunning                => 0x9100

def RunningState.ofRaw? : UInt16 → Option RunningState
  | 0x0000 => some .running0000
  | 0x0001 => some .stop0001
  | 0x0002 => some .keyStop0002
  | 0x0004 => some .emergencyStop0004
  | 0x0008 => some .standby0008
  | 0x0010 => some .initialStandby0010
  | 0x0014 => some .microgridOperation
  | 0x0020 => some .starting0020
  | 0x0040 => some .running0040
  | 0x0041 => some .offGridCharge
  | 0x0080 => some .deratingRunning0080
  | 0x0100 => some .fault0100
  | 0x0200 => some .updateFailed
  | 0x0400 => some .maintainMode
  | 0x0800 => some .forcedMode
  | 0x1000 => some .runningOffGrid
  | 0x1111 => some .uninitialized
  | 0x1200 => some .initialStandby1200
  | 0x1300 => some .keyStop1300
  | 0x1400 => some .standby1400
  | 0x1500 => some .emergencyStop1500
  | 0x1600 => some .starting1600
  | 0x1700 => some .afciSelfTestShutdown
  | 0x1800 => some .intelligentStationBuilding
  | 0x1900 => some .safeMode
  | 0x2000 => some .openLoop
  | 0x2500 => some .communicateFault
  | 0x2501 => some .restarting
  | 0x4000 => some .externalEMSMode
  | 0x4001 => some .emergencyCharging
  | 0x5500 => some .fault5500
  | 0x8000 => some .stop8000
  | 0x8100 => some .deratingRunning8100
  | 0x8200 => some .dispatchRunning
  | 0x9100 => some .warnRunning
  | _      => none

/-- The YAML's label, verbatim. Not injective: see the type's docstring. -/
def RunningState.label : RunningState → String
  | .running0000                => "Running"
  | .stop0001                   => "Stop"
  | .keyStop0002                => "Key stop"
  | .emergencyStop0004          => "Emergency Stop"
  | .standby0008                => "Standby"
  | .initialStandby0010         => "Initial standby"
  | .microgridOperation         => "Microgrid Operation"
  | .starting0020               => "Starting"
  | .running0040                => "Running"
  | .offGridCharge              => "Off-grid Charge"
  | .deratingRunning0080        => "Derating Running"
  | .fault0100                  => "Fault"
  | .updateFailed               => "Update Failed"
  | .maintainMode               => "Running in maintain mode"
  | .forcedMode                 => "Running in compulsory (forced) mode"
  | .runningOffGrid             => "Running (off-grid)"
  | .uninitialized              => "Uninitialized"
  | .initialStandby1200         => "Initial standby"
  | .keyStop1300                => "Key stop"
  | .standby1400                => "Standby"
  | .emergencyStop1500          => "Emergency Stop"
  | .starting1600               => "Starting"
  | .afciSelfTestShutdown       => "AFCI self-test shutdown"
  | .intelligentStationBuilding => "Intelligent Station Building Status"
  | .safeMode                   => "Safe Mode"
  | .openLoop                   => "Open loop"
  | .communicateFault           => "Communicate fault"
  | .restarting                 => "Restarting"
  | .externalEMSMode            => "Running in External EMS mode"
  | .emergencyCharging          => "Emergency Charging Operation"
  | .fault5500                  => "Fault"
  | .stop8000                   => "Stop"
  | .deratingRunning8100        => "Derating Running"
  | .dispatchRunning            => "Dispatch Running"
  | .warnRunning                => "Warn Running"

/-- The YAML template's fallback for codes outside the table. -/
def RunningState.labelRaw (v : UInt16) : String :=
  match RunningState.ofRaw? v with
  | some s => s.label
  | none   => s!"Unknown running state code: 0x{(v.toBitVec.toHex)}"

theorem RunningState.ofRaw?_toRaw (s : RunningState) : RunningState.ofRaw? s.toRaw = some s := by
  cases s <;> rfl

theorem RunningState.toRaw_of_ofRaw? {v : UInt16} {s : RunningState}
    (h : RunningState.ofRaw? v = some s) : s.toRaw = v := by
  unfold RunningState.ofRaw? at h
  split at h <;> cases h <;> rfl

-- The two states seen on the real inverter during the forced-charge test.
#guard RunningState.ofRaw? 2048 == some .forcedMode
#guard RunningState.ofRaw? 0    == some .running0000
#guard RunningState.labelRaw 0x0042 == "Unknown running state code: 0x0042"

end Sungrowd
