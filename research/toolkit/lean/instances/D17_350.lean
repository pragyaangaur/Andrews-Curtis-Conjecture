import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 350 of the cap-17 certificate: slots 179200 .. 179711 -/
theorem chk_350 : chunkCheck 17 T stdSt 179200 512 = true := by decide +kernel

end Row17
