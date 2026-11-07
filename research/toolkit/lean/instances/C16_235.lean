import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 235 of the cap-16 certificate: slots 240640 .. 241663 -/
theorem chk_235 : chunkCheck 16 T stdSt 240640 1024 = true := by decide +kernel

end Row16
