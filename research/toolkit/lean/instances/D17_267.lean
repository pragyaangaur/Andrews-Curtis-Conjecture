import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 267 of the cap-17 certificate: slots 136704 .. 137215 -/
theorem chk_267 : chunkCheck 17 T stdSt 136704 512 = true := by decide +kernel

end Row17
