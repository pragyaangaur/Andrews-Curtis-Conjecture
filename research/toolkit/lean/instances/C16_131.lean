import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 131 of the cap-16 certificate: slots 134144 .. 135167 -/
theorem chk_131 : chunkCheck 16 T stdSt 134144 1024 = true := by decide +kernel

end Row16
