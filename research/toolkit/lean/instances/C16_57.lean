import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 57 of the cap-16 certificate: slots 58368 .. 59391 -/
theorem chk_57 : chunkCheck 16 T stdSt 58368 1024 = true := by decide +kernel

end Row16
