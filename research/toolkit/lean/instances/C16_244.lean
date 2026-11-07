import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 244 of the cap-16 certificate: slots 249856 .. 250879 -/
theorem chk_244 : chunkCheck 16 T stdSt 249856 1024 = true := by decide +kernel

end Row16
