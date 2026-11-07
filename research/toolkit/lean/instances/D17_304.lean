import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 304 of the cap-17 certificate: slots 155648 .. 156159 -/
theorem chk_304 : chunkCheck 17 T stdSt 155648 512 = true := by decide +kernel

end Row17
