import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 152 of the cap-16 certificate: slots 155648 .. 156671 -/
theorem chk_152 : chunkCheck 16 T stdSt 155648 1024 = true := by decide +kernel

end Row16
