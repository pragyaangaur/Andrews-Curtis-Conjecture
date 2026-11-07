import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 8 of the cap-16 certificate: slots 8192 .. 9215 -/
theorem chk_8 : chunkCheck 16 T stdSt 8192 1024 = true := by decide +kernel

end Row16
