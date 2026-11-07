import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 374 of the cap-17 certificate: slots 191488 .. 191999 -/
theorem chk_374 : chunkCheck 17 T stdSt 191488 512 = true := by decide +kernel

end Row17
