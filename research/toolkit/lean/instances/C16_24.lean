import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 24 of the cap-16 certificate: slots 24576 .. 25599 -/
theorem chk_24 : chunkCheck 16 T stdSt 24576 1024 = true := by decide +kernel

end Row16
