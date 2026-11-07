import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 99 of the cap-17 certificate: slots 50688 .. 51199 -/
theorem chk_99 : chunkCheck 17 T stdSt 50688 512 = true := by decide +kernel

end Row17
