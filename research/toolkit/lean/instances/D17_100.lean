import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 100 of the cap-17 certificate: slots 51200 .. 51711 -/
theorem chk_100 : chunkCheck 17 T stdSt 51200 512 = true := by decide +kernel

end Row17
