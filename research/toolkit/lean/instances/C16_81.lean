import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 81 of the cap-16 certificate: slots 82944 .. 83967 -/
theorem chk_81 : chunkCheck 16 T stdSt 82944 1024 = true := by decide +kernel

end Row16
