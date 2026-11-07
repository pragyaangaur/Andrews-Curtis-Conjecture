import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 118 of the cap-17 certificate: slots 60416 .. 60927 -/
theorem chk_118 : chunkCheck 17 T stdSt 60416 512 = true := by decide +kernel

end Row17
