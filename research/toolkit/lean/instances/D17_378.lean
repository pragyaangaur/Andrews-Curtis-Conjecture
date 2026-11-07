import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 378 of the cap-17 certificate: slots 193536 .. 194047 -/
theorem chk_378 : chunkCheck 17 T stdSt 193536 512 = true := by decide +kernel

end Row17
