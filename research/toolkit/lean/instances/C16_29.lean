import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 29 of the cap-16 certificate: slots 29696 .. 30719 -/
theorem chk_29 : chunkCheck 16 T stdSt 29696 1024 = true := by decide +kernel

end Row16
