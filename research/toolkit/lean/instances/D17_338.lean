import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 338 of the cap-17 certificate: slots 173056 .. 173567 -/
theorem chk_338 : chunkCheck 17 T stdSt 173056 512 = true := by decide +kernel

end Row17
