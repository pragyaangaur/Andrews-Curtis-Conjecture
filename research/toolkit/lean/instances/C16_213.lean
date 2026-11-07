import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 213 of the cap-16 certificate: slots 218112 .. 219135 -/
theorem chk_213 : chunkCheck 16 T stdSt 218112 1024 = true := by decide +kernel

end Row16
