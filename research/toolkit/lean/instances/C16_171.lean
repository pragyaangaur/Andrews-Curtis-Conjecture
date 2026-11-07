import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 171 of the cap-16 certificate: slots 175104 .. 176127 -/
theorem chk_171 : chunkCheck 16 T stdSt 175104 1024 = true := by decide +kernel

end Row16
