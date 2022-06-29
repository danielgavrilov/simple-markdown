(function (global, factory) {
typeof exports === 'object' && typeof module !== 'undefined' ? module.exports = factory() :
typeof define === 'function' && define.amd ? define(factory) :
(global = global || self, global.SimpleMarkdown = factory());
}(this, (function () { 'use strict';

/* @flow */
/* @ts-check */

/**
 * Simple-Markdown
 * ===============
 *
 * Simple-Markdown's primary goal is to be easy to adapt. It aims
 * to be compliant with John Gruber's [Markdown Syntax page][1],
 * but compatiblity with other markdown implementations' edge-cases
 * will be sacrificed where it conflicts with simplicity or
 * extensibility.
 *
 * If your goal is to simply embed a standard markdown implementation
 * in your website, simple-markdown is probably not the best library
 * for you (although it should work). But if you have struggled to
 * customize an existing library to meet your needs, simple-markdown
 * might be able to help.
 *
 * Many of the regexes and original logic has been adapted from
 * the wonderful [marked.js](https://github.com/chjj/marked)
 *
 * LICENSE (MIT):
 * New code copyright (c) 2014-2019 Khan Academy & Aria Buckles.
 *
 * Portions adapted from marked.js copyright (c) 2011-2014
 * Christopher Jeffrey (https://github.com/chjj/).
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

// Typescript language & simple-markdown.d.ts references:
/// <reference lib="ES2018" />
/// <reference path="../simple-markdown.d.ts" />

/*::
// Flow Type Definitions:

type Capture =
    Array<string> & {index: number} |
    Array<string> & {index?: number};

type Attr = string | number | boolean | null | void;

type SingleASTNode = {
    type: string,
    [string]: any,
};

type UnTypedASTNode = {
    [string]: any
};

type ASTNode = SingleASTNode | Array<SingleASTNode>;

type State = {
    key?: string | number | void,
    inline?: ?boolean,
    [string]: any,
};

type ReactElement = React$Element<any>;
type ReactElements = React$Node;

type MatchFunction = { regex?: RegExp } & (
    source: string,
    state: State,
    prevCapture: string
) => ?Capture;

type Parser = (
    source: string,
    state?: ?State
) => Array<SingleASTNode>;

type ParseFunction = (
    capture: Capture,
    nestedParse: Parser,
    state: State,
) => (UnTypedASTNode | ASTNode);

type SingleNodeParseFunction = (
    capture: Capture,
    nestedParse: Parser,
    state: State,
) => UnTypedASTNode;

type Output<Result> = (
    node: ASTNode,
    state?: ?State
) => Result;

type NodeOutput<Result> = (
    node: SingleASTNode,
    nestedOutput: Output<Result>,
    state: State
) => Result;

type ArrayNodeOutput<Result> = (
    node: Array<SingleASTNode>,
    nestedOutput: Output<Result>,
    state: State
) => Result;

type ReactOutput = Output<ReactElements>;
type ReactNodeOutput = NodeOutput<ReactElements>;
type HtmlOutput = Output<string>;
type HtmlNodeOutput = NodeOutput<string>;

type ParserRule = {
    +order: number,
    +match: MatchFunction,
    +quality?: (capture: Capture, state: State, prevCapture: string) => number,
    +parse: ParseFunction,
};

type SingleNodeParserRule = {
    +order: number,
    +match: MatchFunction,
    +quality?: (capture: Capture, state: State, prevCapture: string) => number,
    +parse: SingleNodeParseFunction,
};

type ReactOutputRule = {
    // we allow null because some rules are never output results, and that's
    // legal as long as no parsers return an AST node matching that rule.
    // We don't use ? because this makes it be explicitly defined as either
    // a valid function or null, so it can't be forgotten.
    +react: ReactNodeOutput | null,
};

type HtmlOutputRule = {
    +html: HtmlNodeOutput | null,
};

type ArrayRule = {
    +react?: ArrayNodeOutput<ReactElements>,
    +html?: ArrayNodeOutput<string>,
    +[string]: ArrayNodeOutput<any>,
};

type ParserRules = {
    +Array?: ArrayRule,
    +[type: string]: ParserRule,
};

type OutputRules<Rule> = {
    +Array?: ArrayRule,
    +[type: string]: Rule
};
type Rules<OutputRule> = {
    +Array?: ArrayRule,
    +[type: string]: ParserRule & OutputRule,
};
type ReactRules = {
    +Array?: {
        +react: ArrayNodeOutput<ReactElements>,
    },
    +[type: string]: ParserRule & ReactOutputRule,
};
type HtmlRules = {
    +Array?: {
        +html: ArrayNodeOutput<string>,
    },
    +[type: string]: ParserRule & HtmlOutputRule,
};

// We want to clarify our defaultRules types a little bit more so clients can
// reuse defaultRules built-ins. So we make some stronger guarantess when
// we can:
type NonNullReactOutputRule = {
    +react: ReactNodeOutput,
};
type ElementReactOutputRule = {
    +react: NodeOutput<ReactElement>,
};
type TextReactOutputRule = {
    +react: NodeOutput<string>,
};
type NonNullHtmlOutputRule = {
    +html: HtmlNodeOutput,
};

type DefaultInRule = SingleNodeParserRule & ReactOutputRule & HtmlOutputRule;
type TextInOutRule = SingleNodeParserRule & TextReactOutputRule & NonNullHtmlOutputRule;
type LenientInOutRule = SingleNodeParserRule & NonNullReactOutputRule & NonNullHtmlOutputRule;
type DefaultInOutRule = SingleNodeParserRule & ElementReactOutputRule & NonNullHtmlOutputRule;

type DefaultRules = {
    +Array: {
        +react: ArrayNodeOutput<ReactElements>,
        +html: ArrayNodeOutput<string>
    },
    +escape: DefaultInRule,
    +url: DefaultInRule,
    +link: DefaultInOutRule,
    +em: DefaultInOutRule,
    +strong: DefaultInOutRule,
    +u: DefaultInOutRule,
    +br: DefaultInOutRule,
    +text: TextInOutRule,
};

type RefNode = {
    type: string,
    content?: ASTNode,
    target?: string,
    title?: string,
    alt?: string,
};

// End Flow Definitions
*/

var CR_NEWLINE_R = /\r\n?/g;
var TAB_R = /\t/g;
var FORMFEED_R = /\f/g;

/**
 * Turn various whitespace into easy-to-process whitespace
 * @param {string} source
 * @returns {string}
 */
var preprocess = function(source /* : string */) {
    return source.replace(CR_NEWLINE_R, '\n')
            .replace(FORMFEED_R, '')
            .replace(TAB_R, '    ');
};

/**
 * @param {SimpleMarkdown.OptionalState} givenState
 * @param {SimpleMarkdown.OptionalState} defaultState
 * @returns {SimpleMarkdown.State}
 */
var populateInitialState = function(
    givenState /* : ?State */,
    defaultState /* : ?State */
) /* : State */{
    var state /* : State */ = givenState || {};
    if (defaultState != null) {
        for (var prop in defaultState) {
            if (Object.prototype.hasOwnProperty.call(defaultState, prop)) {
                state[prop] = defaultState[prop];
            }
        }
    }
    return state;
};

/**
 * Creates a parser for a given set of rules, with the precedence
 * specified as a list of rules.
 *
 * @param {SimpleMarkdown.ParserRules} rules
 *     an object containing
 *     rule type -> {match, order, parse} objects
 *     (lower order is higher precedence)
 * @param {SimpleMarkdown.OptionalState} [defaultState]
 *
 * @returns {SimpleMarkdown.Parser}
 *     The resulting parse function, with the following parameters:
 *     @source: the input source string to be parsed
 *     @state: an optional object to be threaded through parse
 *         calls. Allows clients to add stateful operations to
 *         parsing, such as keeping track of how many levels deep
 *         some nesting is. For an example use-case, see passage-ref
 *         parsing in src/widgets/passage/passage-markdown.jsx
 */
var parserFor = function(rules /*: ParserRules */, defaultState /*: ?State */) {
    // Sorts rules in order of increasing order, then
    // ascending rule name in case of ties.
    var ruleList = Object.keys(rules).filter(function(type) {
        var rule = rules[type];
        if (rule == null || rule.match == null) {
            return false;
        }
        var order = rule.order;
        if ((typeof order !== 'number' || !isFinite(order)) &&
                typeof console !== 'undefined') {
            console.warn(
                "simple-markdown: Invalid order for rule `" + type + "`: " +
                String(order)
            );
        }
        return true;
    });

    ruleList.sort(function(typeA, typeB) {
        var ruleA /* : ParserRule */ = /** @type {SimpleMarkdown.ParserRule} */ (rules[typeA] /*:: :any */);
        var ruleB /* : ParserRule */ = /** @type {SimpleMarkdown.ParserRule} */ (rules[typeB] /*:: :any */);
        var orderA = ruleA.order;
        var orderB = ruleB.order;

        // First sort based on increasing order
        if (orderA !== orderB) {
            return orderA - orderB;
        }

        var secondaryOrderA = ruleA.quality ? 0 : 1;
        var secondaryOrderB = ruleB.quality ? 0 : 1;

        if (secondaryOrderA !== secondaryOrderB) {
            return secondaryOrderA - secondaryOrderB;

        // Then based on increasing unicode lexicographic ordering
        } else if (typeA < typeB) {
            return -1;
        } else if (typeA > typeB) {
            return 1;

        } else {
            // Rules should never have the same name,
            // but this is provided for completeness.
            return 0;
        }
    });

    /** @type {SimpleMarkdown.State} */
    var latestState;
    /** @type {SimpleMarkdown.Parser} */
    var nestedParse = function(source /* : string */, state /* : ?State */) {
        /** @type Array<SimpleMarkdown.SingleASTNode> */
        var result = [];
        state = state || latestState;
        latestState = state;
        while (source) {
            // store the best match, it's rule, and quality:
            var ruleType = null;
            var rule = null;
            var capture = null;
            var quality = NaN;

            // loop control variables:
            var i = 0;
            var currRuleType = ruleList[0];
            var currRule /* : ParserRule */ = /** @type {SimpleMarkdown.ParserRule} */ ( rules[currRuleType] /*:: :any */ );

            do {
                var currOrder = currRule.order;
                var prevCaptureStr = state.prevCapture == null ? "" : state.prevCapture[0];
                var currCapture = currRule.match(source, state, prevCaptureStr);

                if (currCapture) {
                    var currQuality = currRule.quality ? currRule.quality(
                        currCapture,
                        state,
                        prevCaptureStr
                    ) : 0;
                    // This should always be true the first time because
                    // the initial quality is NaN (that's why there's the
                    // condition negation).
                    if (!(currQuality <= quality)) {
                        ruleType = currRuleType;
                        rule = currRule;
                        capture = currCapture;
                        quality = currQuality;
                    }
                }

                // Move on to the next item.
                // Note that this makes `currRule` be the next item
                i++;
                currRuleType = ruleList[i];
                currRule = /*::((*/ /** @type {SimpleMarkdown.ParserRule} */ (rules[currRuleType]) /*:: : any) : ParserRule)*/;

            } while (
                // keep looping while we're still within the ruleList
                currRule && (
                    // if we don't have a match yet, continue
                    !capture || (
                        // or if we have a match, but the next rule is
                        // at the same order, and has a quality measurement
                        // functions, then this rule must have a quality
                        // measurement function (since they are sorted before
                        // those without), and we need to check if there is
                        // a better quality match
                        currRule.order === currOrder &&
                        currRule.quality
                    )
                )
            );

            // TODO(aria): Write tests for these
            if (rule == null || capture == null /*:: || ruleType == null */) {
                throw new Error(
                    "Could not find a matching rule for the below " +
                    "content. The rule with highest `order` should " +
                    "always match content provided to it. Check " +
                    "the definition of `match` for '" +
                    ruleList[ruleList.length - 1] +
                    "'. It seems to not match the following source:\n" +
                    source
                );
            }
            if (capture.index) { // If present and non-zero, i.e. a non-^ regexp result:
                throw new Error(
                    "`match` must return a capture starting at index 0 " +
                    "(the current parse index). Did you forget a ^ at the " +
                    "start of the RegExp?"
                );
            }

            var parsed = rule.parse(capture, nestedParse, state);
            // We maintain the same object here so that rules can
            // store references to the objects they return and
            // modify them later. (oops sorry! but this adds a lot
            // of power--see reflinks.)
            if (Array.isArray(parsed)) {
                Array.prototype.push.apply(result, parsed);
            } else {
                // We also let rules override the default type of
                // their parsed node if they would like to, so that
                // there can be a single output function for all links,
                // even if there are several rules to parse them.
                if (parsed.type == null) {
                    parsed.type = ruleType;
                }
                result.push(/** @type {SimpleMarkdown.SingleASTNode} */ (parsed));
            }

            state.prevCapture = capture;
            source = source.substring(state.prevCapture[0].length);
        }
        return result;
    };

    /** @type {SimpleMarkdown.Parser} */
    var outerParse = function(source /* : string */, state /* : ?State */) {
        latestState = populateInitialState(state, defaultState);
        if (!latestState.inline && !latestState.disableAutoBlockNewlines) {
            source = source + "\n\n";
        }
        // We store the previous capture so that match functions can
        // use some limited amount of lookbehind. Lists use this to
        // ensure they don't match arbitrary '- ' or '* ' in inline
        // text (see the list rule for more information). This stores
        // the full regex capture object, if there is one.
        latestState.prevCapture = null;
        return nestedParse(preprocess(source), latestState);
    };
    return outerParse;
};

// Creates a match function for an inline scoped element from a regex
/** @type {(regex: RegExp) => SimpleMarkdown.MatchFunction} */
var inlineRegex = function(regex /* : RegExp */) {
    /** @type {SimpleMarkdown.MatchFunction} */
    var match /* : MatchFunction */ = function(source, state) {
        if (state.inline) {
            return regex.exec(source);
        } else {
            return null;
        }
    };
    match.regex = regex;
    return match;
};

// Creates a match function for a block scoped element from a regex
/** @type {(regex: RegExp) => SimpleMarkdown.MatchFunction} */
var blockRegex = function(regex /* : RegExp */) {
    /** @type {SimpleMarkdown.MatchFunction} */
    var match /* : MatchFunction */ = function(source, state) {
        if (state.inline) {
            return null;
        } else {
            return regex.exec(source);
        }
    };
    match.regex = regex;
    return match;
};

// Creates a match function from a regex, ignoring block/inline scope
/** @type {(regex: RegExp) => SimpleMarkdown.MatchFunction} */
var anyScopeRegex = function(regex /* : RegExp */) {
    /** @type {SimpleMarkdown.MatchFunction} */
    var match /* : MatchFunction */ = function(source, state) {
        return regex.exec(source);
    };
    match.regex = regex;
    return match;
};

var TYPE_SYMBOL =
    (typeof Symbol === 'function' && Symbol.for &&
     Symbol.for('react.element')) ||
    0xeac7;

/**
 * @param {string} type
 * @param {string | number | null | undefined} key
 * @param {Object<string, any>} props
 * @returns {SimpleMarkdown.ReactElement}
 */
var reactElement = function(
    type /* : string */,
    key /* : string | number | null | void */,
    props /* : { [string]: any } */
) /* : ReactElement */ {
    var element /* : ReactElement */ = /** @type {SimpleMarkdown.ReactElement} */ ({
        $$typeof: TYPE_SYMBOL,
        type: type,
        key: key == null ? undefined : key,
        ref: null,
        props: props,
        _owner: null
    } /* : any */);
    return element;
};

/** Returns a closed HTML tag.
 * @param {string} tagName - Name of HTML tag (eg. "em" or "a")
 * @param {string} content - Inner content of tag
 * @param {{ [attr: string]: SimpleMarkdown.Attr }} [attributes] - Optional extra attributes of tag as an object of key-value pairs
 *   eg. { "href": "http://google.com" }. Falsey attributes are filtered out.
 * @param {boolean} [isClosed] - boolean that controls whether tag is closed or not (eg. img tags).
 *   defaults to true
 */
var htmlTag = function(
    tagName /* : string */,
    content /* : string */,
    attributes /* : ?{[any]: ?Attr} */,
    isClosed /* : ?boolean */
) {
    attributes = attributes || {};
    isClosed = typeof isClosed !== 'undefined' ? isClosed : true;

    var attributeString = "";
    for (var attr in attributes) {
        var attribute = attributes[attr];
        // Removes falsey attributes
        if (Object.prototype.hasOwnProperty.call(attributes, attr) &&
                attribute) {
            attributeString += " " +
                sanitizeText(attr) + '="' +
                sanitizeText(attribute) + '"';
        }
    }

    var unclosedTag = "<" + tagName + attributeString + ">";

    if (isClosed) {
        return unclosedTag + content + "</" + tagName + ">";
    } else {
        return unclosedTag;
    }
};

var EMPTY_PROPS = {};

/**
 * @param {string | null | undefined} url - url to sanitize
 * @returns {string | null} - url if safe, or null if a safe url could not be made
 */
var sanitizeUrl = function(url /* : ?string */) {
    if (url == null) {
        return null;
    }
    try {
        var prot = new URL(url, 'https://localhost').protocol;
        if (prot.indexOf('javascript:') === 0 || prot.indexOf('vbscript:') === 0 || prot.indexOf('data:') === 0) {
            return null;
        }
    } catch (e) {
        // invalid URLs should throw a TypeError
        // see for instance: `new URL("");`
        return null;
    }
    return url;
};

var SANITIZE_TEXT_R = /[<>&"']/g;
/** @type {any} */
var SANITIZE_TEXT_CODES = {
    '<': '&lt;',
    '>': '&gt;',
    '&': '&amp;',
    '"': '&quot;',
    "'": '&#x27;',
    '/': '&#x2F;',
    "`": '&#96;'
};
/**
 * @param {SimpleMarkdown.Attr} text
 * @returns {string}
 */
var sanitizeText = function(text /* : Attr */) {
    return String(text).replace(SANITIZE_TEXT_R, function(chr) {
        return SANITIZE_TEXT_CODES[chr];
    });
};

var UNESCAPE_URL_R = /\\([^0-9A-Za-z\s])/g;

/**
 * @param {string} rawUrlString
 * @returns {string}
 */
var unescapeUrl = function(rawUrlString /* : string */) {
    return rawUrlString.replace(UNESCAPE_URL_R, "$1");
};

/**
 * Parse some content with the parser `parse`, with state.inline
 * set to true. Useful for block elements; not generally necessary
 * to be used by inline elements (where state.inline is already true.
 *
 * @param {SimpleMarkdown.Parser} parse
 * @param {string} content
 * @param {SimpleMarkdown.State} state
 * @returns {SimpleMarkdown.ASTNode}
 */
var parseInline = function(parse, content, state) {
    var isCurrentlyInline = state.inline || false;
    state.inline = true;
    var result = parse(content, state);
    state.inline = isCurrentlyInline;
    return result;
};
/**
 * @param {SimpleMarkdown.Parser} parse
 * @param {string} content
 * @param {SimpleMarkdown.State} state
 * @returns {SimpleMarkdown.ASTNode}
 */
var parseBlock = function(parse, content, state) {
    var isCurrentlyInline = state.inline || false;
    state.inline = false;
    var result = parse(content + "\n\n", state);
    state.inline = isCurrentlyInline;
    return result;
};

/**
 * @param {SimpleMarkdown.Capture} capture
 * @param {SimpleMarkdown.Parser} parse
 * @param {SimpleMarkdown.State} state
 * @returns {SimpleMarkdown.UnTypedASTNode}
 */
var parseCaptureInline = function(capture, parse, state) {
    return {
        content: parseInline(parse, capture[1], state)
    };
};
/**
 * @returns {SimpleMarkdown.UnTypedASTNode}
 */
var ignoreCapture = function() { return {}; };
var BLOCK_END_R = /\n{2,}$/;

var LINK_INSIDE = "(?:\\[[^\\]]*\\]|[^\\[\\]]|\\](?=[^\\[]*\\]))*";
var LINK_HREF_AND_TITLE =
        "\\s*<?((?:\\([^)]*\\)|[^\\s\\\\]|\\\\.)*?)>?(?:\\s+['\"]([\\s\\S]*?)['\"])?\\s*";

var currOrder = 0;
/** @type {SimpleMarkdown.DefaultRules} */
var defaultRules /* : DefaultRules */ = {
    Array: {
        react: function(arr, output, state) {
            var oldKey = state.key;
            var result /* : Array<ReactElements> */ = [];

            // map output over the ast, except group any text
            // nodes together into a single string output.
            for (var i = 0, key = 0; i < arr.length; i++, key++) {
                // `key` is our numerical `state.key`, which we increment for
                // every output node, but don't change for joined text nodes.
                // (i, however, must change for joined text nodes)
                state.key = '' + i;

                var node = arr[i];
                if (node.type === 'text') {
                    node = { type: 'text', content: node.content };
                    for (; i + 1 < arr.length && arr[i + 1].type === 'text'; i++) {
                        node.content += arr[i + 1].content;
                    }
                }

                result.push(output(node, state));
            }

            state.key = oldKey;
            return result;
        },
        html: function(arr, output, state) {
            var result = "";

            // map output over the ast, except group any text
            // nodes together into a single string output.
            for (var i = 0; i < arr.length; i++) {

                var node = arr[i];
                if (node.type === 'text') {
                    node = { type: 'text', content: node.content };
                    for (; i + 1 < arr.length && arr[i + 1].type === 'text'; i++) {
                        node.content += arr[i + 1].content;
                    }
                }

                result += output(node, state);
            }
            return result;
        }
    },
    paragraph: {
        order: currOrder++,
        match: blockRegex(/^((?:[^\n]|\n(?! *\n))+)(?:\n *)+\n/),
        parse: parseCaptureInline,
        react: function(node, output, state) {
            return reactElement(
                'div',
                state.key,
                {
                    className: 'paragraph',
                    children: output(node.content, state)
                }
            );
        },
        html: function(node, output, state) {
            var attributes = {
                class: 'paragraph'
            };
            return htmlTag("div", output(node.content, state), attributes);
        }
    },
    escape: {
        order: currOrder++,
        // We don't allow escaping numbers, letters, or spaces here so that
        // backslashes used in plain text still get rendered. But allowing
        // escaping anything else provides a very flexible escape mechanism,
        // regardless of how this grammar is extended.
        match: inlineRegex(/^\\([^0-9A-Za-z\s])/),
        parse: function(capture, parse, state) {
            return {
                type: "text",
                content: capture[1]
            };
        },
        react: null,
        html: null
    },
    url: {
        order: currOrder++,
        match: inlineRegex(/^(https?:\/\/[^\s<]+[^<.,:;"')\]\s])/),
        parse: function(capture, parse, state) {
            return {
                type: "link",
                content: [{
                    type: "text",
                    content: capture[1]
                }],
                target: capture[1],
                title: undefined
            };
        },
        react: null,
        html: null
    },
    link: {
        order: currOrder++,
        match: inlineRegex(new RegExp(
            "^\\[(" + LINK_INSIDE + ")\\]\\(" + LINK_HREF_AND_TITLE + "\\)"
        )),
        parse: function(capture, parse, state) {
            var link ={
                content: parse(capture[1], state),
                target: unescapeUrl(capture[2]),
                title: capture[3]
            };
            return link;
        },
        react: function(node, output, state) {
            return reactElement(
                'a',
                state.key,
                {
                    href: sanitizeUrl(node.target),
                    title: node.title,
                    children: output(node.content, state)
                }
            );
        },
        html: function(node, output, state) {
            var attributes = {
                href: sanitizeUrl(node.target),
                title: node.title
            };

            return htmlTag("a", output(node.content, state), attributes);
        }
    },
    em: {
        order: currOrder /* same as strong/u */,
        match: inlineRegex(
            new RegExp(
                // only match _s surrounding words.
                "^\\b_" +
                "((?:__|\\\\[\\s\\S]|[^\\\\_])+?)_" +
                "\\b" +
                // Or match *s:
                "|" +
                // Only match *s that are followed by a non-space:
                "^\\*(?=\\S)(" +
                // Match at least one of:
                "(?:" +
                  //  - `**`: so that bolds inside italics don't close the
                  //          italics
                  "\\*\\*|" +
                  //  - escape sequence: so escaped *s don't close us
                  "\\\\[\\s\\S]|" +
                  //  - whitespace: followed by a non-* (we don't
                  //          want ' *' to close an italics--it might
                  //          start a list)
                  "\\s+(?:\\\\[\\s\\S]|[^\\s\\*\\\\]|\\*\\*)|" +
                  //  - non-whitespace, non-*, non-backslash characters
                  "[^\\s\\*\\\\]" +
                ")+?" +
                // followed by a non-space, non-* then *
                ")\\*(?!\\*)"
            )
        ),
        quality: function(capture) {
            // precedence by length, `em` wins ties:
            return capture[0].length + 0.2;
        },
        parse: function(capture, parse, state) {
            return {
                content: parse(capture[2] || capture[1], state)
            };
        },
        react: function(node, output, state) {
            return reactElement(
                'em',
                state.key,
                {
                    children: output(node.content, state)
                }
            );
        },
        html: function(node, output, state) {
            return htmlTag("em", output(node.content, state));
        }
    },
    strong: {
        order: currOrder /* same as em */,
        match: inlineRegex(/^\*\*((?:\\[\s\S]|[^\\])+?)\*\*(?!\*)/),
        quality: function(capture) {
            // precedence by length, wins ties vs `u`:
            return capture[0].length + 0.1;
        },
        parse: parseCaptureInline,
        react: function(node, output, state) {
            return reactElement(
                'strong',
                state.key,
                {
                    children: output(node.content, state)
                }
            );
        },
        html: function(node, output, state) {
            return htmlTag("strong", output(node.content, state));
        }
    },
    u: {
        order: currOrder++ /* same as em&strong; increment for next rule */,
        match: inlineRegex(/^__((?:\\[\s\S]|[^\\])+?)__(?!_)/),
        quality: function(capture) {
            // precedence by length, loses all ties
            return capture[0].length;
        },
        parse: parseCaptureInline,
        react: function(node, output, state) {
            return reactElement(
                'u',
                state.key,
                {
                    children: output(node.content, state)
                }
            );
        },
        html: function(node, output, state) {
            return htmlTag("u", output(node.content, state));
        }
    },
    br: {
        order: currOrder++,
        match: anyScopeRegex(/^ {2,}\n/),
        parse: ignoreCapture,
        react: function(node, output, state) {
            return reactElement(
                'br',
                state.key,
                EMPTY_PROPS
            );
        },
        html: function(node, output, state) {
            return "<br>";
        }
    },
    text: {
        order: currOrder++,
        // Here we look for anything followed by non-symbols,
        // double newlines, or double-space-newlines
        // We break on any symbol characters so that this grammar
        // is easy to extend without needing to modify this regex
        match: anyScopeRegex(
            /^[\s\S]+?(?=[^0-9A-Za-z\s\u00c0-\uffff]|\n\n| {2,}\n|\w+:\S|$)/
        ),
        parse: function(capture, parse, state) {
            return {
                content: capture[0]
            };
        },
        react: function(node, output, state) {
            return node.content;
        },
        html: function(node, output, state) {
            return sanitizeText(node.content);
        }
    }
};

/** (deprecated)
 * @param {any} rules
 * @param {any} property
 * @returns {any}
 */
var ruleOutput = function/* :: <Rule : Object> */(
    rules /* : OutputRules<Rule> */,
    property /* : $Keys<Rule> */
) {
    if (!property && typeof console !== "undefined") {
        console.warn("simple-markdown ruleOutput should take 'react' or " +
            "'html' as the second argument."
        );
    }

    /** @type {SimpleMarkdown.NodeOutput<any>} */
    var nestedRuleOutput /* : NodeOutput<any> */ = function(
        ast /* : SingleASTNode */,
        outputFunc /* : Output<any> */,
        state /* : State */
    ) {
        return rules[ast.type][property](ast, outputFunc, state);
    };
    return nestedRuleOutput;
};

/** (deprecated)
 * @param {any} outputFunc
 * @returns {any}
 */
var reactFor = function(outputFunc /* : ReactNodeOutput */) /* : ReactOutput */ {
    /** @type {SimpleMarkdown.ReactOutput} */
    var nestedOutput /* : ReactOutput */ = function(ast, state) {
        state = state || {};
        if (Array.isArray(ast)) {
            var oldKey = state.key;
            var result /* : Array<ReactElements> */ = [];

            // map nestedOutput over the ast, except group any text
            // nodes together into a single string output.
            var lastResult = null;
            for (var i = 0; i < ast.length; i++) {
                state.key = '' + i;
                var nodeOut = nestedOutput(ast[i], state);
                if (typeof nodeOut === "string" && typeof lastResult === "string") {
                    lastResult = lastResult + nodeOut;
                    result[result.length - 1] = lastResult;
                } else {
                    result.push(nodeOut);
                    lastResult = nodeOut;
                }
            }

            state.key = oldKey;
            return result;
        } else {
            return outputFunc(ast, nestedOutput, state);
        }
    };
    return nestedOutput;
};

/** (deprecated)
 * @param {any} outputFunc
 * @returns {any}
 */
var htmlFor = function(outputFunc /* : HtmlNodeOutput */) /* : HtmlOutput */ {
    /** @type {SimpleMarkdown.HtmlOutput} */
    var nestedOutput /* : HtmlOutput */ = function(ast, state) {
        state = state || {};
        if (Array.isArray(ast)) {
            return ast.map(function(node) {
                return nestedOutput(node, state);
            }).join("");
        } else {
            return outputFunc(ast, nestedOutput, state);
        }
    };
    return nestedOutput;
};

/**
 * @type {SimpleMarkdown.OutputFor}
 */
var outputFor = function/* :: <Rule : Object> */(
    rules /* : OutputRules<Rule> */,
    property /* : $Keys<Rule> */,
    defaultState /* : ?State */
) {
    if (!property) {
        throw new Error('simple-markdown: outputFor: `property` must be ' +
            'defined. ' +
            'if you just upgraded, you probably need to replace `outputFor` ' +
            'with `reactFor`'
        );
    }

    /** @type {SimpleMarkdown.State} */
    var latestState;
    /** @type {SimpleMarkdown.ArrayRule} */
    var arrayRule = rules.Array || defaultRules.Array;

    // Tricks to convince tsc that this var is not null:
    var arrayRuleCheck = arrayRule[property];
    if (!arrayRuleCheck) {
        throw new Error('simple-markdown: outputFor: to join nodes of type `' +
            property + '` you must provide an `Array:` joiner rule with that type, ' +
            'Please see the docs for details on specifying an Array rule.'
        );
    }
    var arrayRuleOutput = arrayRuleCheck;

    /** @type {SimpleMarkdown.Output<any>} */
    var nestedOutput /* : Output<any> */ = function(ast, state) {
        state = state || latestState;
        latestState = state;
        if (Array.isArray(ast)) {
            return arrayRuleOutput(ast, nestedOutput, state);
        } else {
            return rules[ast.type][property](ast, nestedOutput, state);
        }
    };

    /** @type {SimpleMarkdown.Output<any>} */
    var outerOutput = function(ast, state) {
        latestState = populateInitialState(state, defaultState);
        return nestedOutput(ast, latestState);
    };
    return outerOutput;
};

var defaultRawParse = parserFor(defaultRules);
/**
 * @param {string} source
 * @param {SimpleMarkdown.OptionalState} [state]
 * @returns {Array<SimpleMarkdown.SingleASTNode>}
 */
var defaultBlockParse = function(source, state) {
    state = state || {};
    state.inline = false;
    return defaultRawParse(source, state);
};
/**
 * @param {string} source
 * @param {SimpleMarkdown.OptionalState} [state]
 * @returns {Array<SimpleMarkdown.SingleASTNode>}
 */
var defaultInlineParse = function(source, state) {
    state = state || {};
    state.inline = true;
    return defaultRawParse(source, state);
};
/**
 * @param {string} source
 * @param {SimpleMarkdown.OptionalState} [state]
 * @returns {Array<SimpleMarkdown.SingleASTNode>}
 */
var defaultImplicitParse = function(source, state) {
    var isBlock = BLOCK_END_R.test(source);
    state = state || {};
    state.inline = !isBlock;
    return defaultRawParse(source, state);
};

/** @type {SimpleMarkdown.ReactOutput} */
var defaultReactOutput /* : ReactOutput */ = outputFor(defaultRules, "react");
/** @type {SimpleMarkdown.HtmlOutput} */
var defaultHtmlOutput /* : HtmlOutput */ = outputFor(defaultRules, "html");

/**
 * @param {string} source
 * @param {SimpleMarkdown.OptionalState} [state]
 * @returns {SimpleMarkdown.ReactElements}
 */
var markdownToReact = function(source, state) /* : ReactElements */ {
    return defaultReactOutput(defaultBlockParse(source, state), state);
};
/**
 * @param {string} source
 * @param {SimpleMarkdown.OptionalState} [state]
 * @returns {string}
 */
var markdownToHtml = function(source, state) /* : string */ {
    return defaultHtmlOutput(defaultBlockParse(source, state), state);
};

/**
 * @param {SimpleMarkdown.ReactMarkdownProps} props
 * @returns {SimpleMarkdown.ReactElement}
 */
var ReactMarkdown = function(props) {
    /** @type {Object} */
    var divProps = {};

    for (var prop in props) {
        if (prop !== 'source' &&
            Object.prototype.hasOwnProperty.call(props, prop)
        ) {
            divProps[prop] = props[prop];
        }
    }
    divProps.children = markdownToReact(props.source);

    return reactElement(
        'div',
        null,
        divProps
    );
};


/*:: // Flow exports:
type Exports = {
    +defaultRules: DefaultRules,
    +parserFor: (rules: ParserRules, defaultState?: ?State) => Parser,
    +outputFor: <Rule : Object>(rules: OutputRules<Rule>, param: $Keys<Rule>, defaultState?: ?State) => Output<any>,

    +ruleOutput: <Rule : Object>(rules: OutputRules<Rule>, param: $Keys<Rule>) => NodeOutput<any>,
    +reactFor: (ReactNodeOutput) => ReactOutput,
    +htmlFor: (HtmlNodeOutput) => HtmlOutput,

    +inlineRegex: (regex: RegExp) => MatchFunction,
    +blockRegex: (regex: RegExp) => MatchFunction,
    +anyScopeRegex: (regex: RegExp) => MatchFunction,
    +parseInline: (parse: Parser, content: string, state: State) => ASTNode,
    +parseBlock: (parse: Parser, content: string, state: State) => ASTNode,

    +markdownToReact: (source: string, state?: ?State) => ReactElements,
    +markdownToHtml: (source: string, state?: ?State) => string,
    +ReactMarkdown: (props: { source: string, [string]: any }) => ReactElement,

    +defaultRawParse: (source: string, state?: ?State) => Array<SingleASTNode>,
    +defaultBlockParse: (source: string, state?: ?State) => Array<SingleASTNode>,
    +defaultInlineParse: (source: string, state?: ?State) => Array<SingleASTNode>,
    +defaultImplicitParse: (source: string, state?: ?State) => Array<SingleASTNode>,

    +defaultReactOutput: ReactOutput,
    +defaultHtmlOutput: HtmlOutput,

    +preprocess: (source: string) => string,
    +sanitizeText: (text: Attr) => string,
    +sanitizeUrl: (url: ?string) => ?string,
    +unescapeUrl: (url: string) => string,
    +htmlTag: (tagName: string, content: string, attributes: ?{ [any]: ?Attr }, isClosed: ?boolean) => string,
    +reactElement: (type: string, key: string | null, props: { [string]: any }) => ReactElement,
};

export type {
    // Hopefully you shouldn't have to use these, but they're here if you need!
    // Top-level API:
    State,
    Parser,
    Output,
    ReactOutput,
    HtmlOutput,

    // Most of the following types should be considered experimental and
    // subject to change or change names. Again, they shouldn't be necessary,
    // but if they are I'd love to hear how so I can better support them!

    // Individual Rule fields:
    Capture,
    MatchFunction,
    ParseFunction,
    NodeOutput,
    ArrayNodeOutput,
    ReactNodeOutput,

    // Single rules:
    ParserRule,
    ReactOutputRule,
    HtmlOutputRule,

    // Sets of rules:
    ParserRules,
    OutputRules,
    Rules,
    ReactRules,
    HtmlRules,
};
*/

var SimpleMarkdown /* : Exports */ = {
    defaultRules: defaultRules,
    parserFor: parserFor,
    outputFor: outputFor,

    inlineRegex: inlineRegex,
    blockRegex: blockRegex,
    anyScopeRegex: anyScopeRegex,
    parseInline: parseInline,
    parseBlock: parseBlock,

    // default wrappers:
    markdownToReact: markdownToReact,
    markdownToHtml: markdownToHtml,
    ReactMarkdown: ReactMarkdown,

    defaultBlockParse: defaultBlockParse,
    defaultInlineParse: defaultInlineParse,
    defaultImplicitParse: defaultImplicitParse,

    defaultReactOutput: defaultReactOutput,
    defaultHtmlOutput: defaultHtmlOutput,

    preprocess: preprocess,
    sanitizeText: sanitizeText,
    sanitizeUrl: sanitizeUrl,
    unescapeUrl: unescapeUrl,
    htmlTag: htmlTag,
    reactElement: reactElement,

    // deprecated:
    defaultRawParse: defaultRawParse,
    ruleOutput: ruleOutput,
    reactFor: reactFor,
    htmlFor: htmlFor,

    defaultParse: function() {
        if (typeof console !== 'undefined') {
            console.warn('defaultParse is deprecated, please use `defaultImplicitParse`');
        }
        return defaultImplicitParse.apply(null, /** @type {any} */ (arguments));
    },
    defaultOutput: function() {
        if (typeof console !== 'undefined') {
            console.warn('defaultOutput is deprecated, please use `defaultReactOutput`');
        }
        return defaultReactOutput.apply(null, /** @type {any} */ (arguments));
    }
};

return SimpleMarkdown;

})));
