//! Island language skeleton.
//!
//! Keywords declare; actions are static `Module::fn` paths. Full grammar lands later.

use metis_types::MetisError;

/// Placeholder source unit (path + text). Parsing is intentionally stubbed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceFile {
    pub path: String,
    pub text: String,
}

/// Parse outcome for the foundation stub: only accepts non-empty UTF-8 text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseStub {
    pub byte_len: usize,
}

pub fn parse_stub(src: &SourceFile) -> Result<ParseStub, MetisError> {
    if src.text.is_empty() {
        return Err(MetisError::InvalidHandle);
    }
    Ok(ParseStub {
        byte_len: src.text.len(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_empty_accepts_text() {
        let empty = SourceFile {
            path: "a.island".into(),
            text: String::new(),
        };
        assert!(parse_stub(&empty).is_err());
        let ok = SourceFile {
            path: "a.island".into(),
            text: "island ZFC {}".into(),
        };
        assert_eq!(parse_stub(&ok).unwrap().byte_len, ok.text.len());
    }
}
