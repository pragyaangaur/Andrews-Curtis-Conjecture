import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 52 of the cap-16 certificate: slots 53248 .. 54271 -/
theorem chk_52 : chunkCheck 16 T stdSt 53248 1024 = true := by decide +kernel

end Row16
