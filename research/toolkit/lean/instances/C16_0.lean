import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 0 of the cap-16 certificate: slots 0 .. 1023 -/
theorem chk_0 : chunkCheck 16 T stdSt 0 1024 = true := by decide +kernel

end Row16
