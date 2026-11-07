import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 225 of the cap-17 certificate: slots 115200 .. 115711 -/
theorem chk_225 : chunkCheck 17 T stdSt 115200 512 = true := by decide +kernel

end Row17
